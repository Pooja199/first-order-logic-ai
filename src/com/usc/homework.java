package com.usc;

import java.io.*;
import java.time.Duration;
import java.time.Instant;
import java.util.*;

public class homework {

    static Map<String, String> map = new HashMap<>();
    private static List<String> queryList = new ArrayList<>();


    public static void main(String[] args) throws IOException {
        Instant start = Instant.now();
        List<String> answers = new ArrayList<>();
        List<String> kbList = inputReader();
        for (int i = 0; i < kbList.size(); i++) {
            String trimmedString = removeSpace(kbList.get(i));
            kbList.set(i, trimmedString);
        }
        List<String> kbListCnf = convertToCNF(kbList);

        for (int k = 0; k < queryList.size(); k++) {
            ArrayList listCopy = new ArrayList(kbListCnf);
            if (resolution(listCopy, queryList.get(k))) {
                answers.add("TRUE");
            } else {
                answers.add("FALSE");
            }
        }
        writeAnswer(answers);
    }

    private static void writeAnswer(List<String> answers) throws IOException {
        FileWriter fileWriter = new FileWriter("output.txt");
        PrintWriter printWriter = new PrintWriter(fileWriter);

        for (int i = 0; i < answers.size(); i++) {
            printWriter.println(answers.get(i));
        }
        fileWriter.close();
    }

    private static Boolean resolution(List<String> cnfKbList, String query) {
        Instant start = Instant.now();
        if (query.charAt(0) == '~') {
            cnfKbList.add(query.substring(1));
        } else {
            cnfKbList.add("~" + query);
        }
        for (int i = 0; i < cnfKbList.size(); i++) {
            String clauseKb = cnfKbList.get(i);
            if (clauseKb.contains("|")) {
                String[] literals = clauseKb.split("\\|");
                Arrays.sort(literals);
                String modifiedSortedString = String.join("|", literals);
                cnfKbList.set(i, modifiedSortedString);
            }
        }
        while (true) {
            List<String> newClauses = new ArrayList<>();
            for (int i = 0; i < cnfKbList.size() - 1; i++) {
                for (int j = i + 1; j < cnfKbList.size(); j++) {
                    Instant end = Instant.now();
                    long milSecond = Duration.between(start, end).toMillis();
                    if (milSecond >= 20000) {
                        return false;
                    }
                    List<String> resolvents = resolve(cnfKbList.get(i), cnfKbList.get(j));
//                    System.out.println("list of resolvents: " + Arrays.asList(resolvents));
                    if (resolvents.contains("")) {
//                        System.out.println("clauseA: " + cnfKbList.get(i));
//                        System.out.println("clauseB: " + cnfKbList.get(j));
                        return true;
                    }
                    for (String resolvent : resolvents) {
                        String[] literals = resolvent.split("\\|");
                        Arrays.sort(literals);
                        String modifiedSortedString = String.join("|", literals);
                        if (!newClauses.contains(modifiedSortedString)) {
                            newClauses.add(modifiedSortedString);
                        }
                    }
                }
            }
            if (isSubsetOf(newClauses, cnfKbList)) {
                return false;
            }
            cnfKbList.addAll(newClauses);
        }
    }

    /*
        true : loop stops - ALL sentences in clausesList is in KB
        false : loop continues - even 1 sentence in clausesList is not in KB
     */
    private static Boolean isSubsetOf(List<String> clausesList, List<String> kbListCNF) {
        for (int i = 0; i < kbListCNF.size(); i++) {
            String clauseKb = kbListCNF.get(i);
            String[] literals = clauseKb.split("\\|");
            Arrays.sort(literals);
            String modifiedSortedString = String.join("|", literals);
            kbListCNF.set(i, modifiedSortedString);
        }
        for (String clause : clausesList) {
            String[] literals = clause.split("\\|");
            Arrays.sort(literals);
            String modifiedSortedString = String.join("|", literals);
            if (!kbListCNF.contains(modifiedSortedString)) {
                return false;
            }
        }
        return true;
    }

    private static List<String> resolve(String clauseA, String clauseB) {
        List<String> resolvedClauses = new ArrayList<>();
        String[] clauseALiteralsArray;
        String[] clauseBLiteralsArray;
        clauseALiteralsArray = clauseA.split("\\|");
        clauseBLiteralsArray = clauseB.split("\\|");
        for (int i = 0; i < clauseALiteralsArray.length; i++) {
            String literalA = clauseALiteralsArray[i];
//            System.out.println("literal" + literalA);
            String[] literalAParameters = literalA.substring(literalA.indexOf('(') + 1, literalA.indexOf(')')).split(",");
            String prefix = literalA.substring(0, literalA.indexOf('('));
            for (int j = 0; j < clauseBLiteralsArray.length; j++) {
                String literalB = clauseBLiteralsArray[j];
                Map<String, String> variableConstantMapping = new HashMap<>();
                String[] literalBParameters = literalB.substring(literalB.indexOf('(') + 1, literalB.indexOf(')')).split(",");
                if ((prefix.charAt(0) == '~' && literalB.charAt(0) != '~' && isSameLiteral(prefix.substring(1), literalB.substring(0, literalB.indexOf('(')))) ||
                        (prefix.charAt(0) != '~' && literalB.charAt(0) == '~' && isSameLiteral(prefix, literalB.substring(1, literalB.indexOf('('))))) {
                    if (unification(literalAParameters, literalBParameters, variableConstantMapping)) {
                        List<String> literalResult = new ArrayList<>();
                        for (String literal : clauseALiteralsArray) {
                            if (!literalA.equals(literal)) {
                                String literalModified = "";
                                String prefixBreak = literal.substring(0, literal.indexOf('('));
                                String[] params = literal.substring(literal.indexOf('(') + 1, literal.indexOf(')')).split(",");
                                for (Map.Entry<String, String> entry : variableConstantMapping.entrySet()) {
                                    String key = entry.getKey();
                                    String value = entry.getValue();
                                    for (int m = 0; m < params.length; m++) {
                                        if (params[m].equals(key)) {
                                            params[m] = value;
                                        }
                                    }
                                }
                                literalModified = prefixBreak + "(" + String.join(",", params) + ")";
                                literalResult.add(literalModified);
                            }
                        }
                        for (int k = 0; k < clauseBLiteralsArray.length; k++) {
                            if (!literalB.equals(clauseBLiteralsArray[k])) {
                                String literalModified2 = "";
                                String literal = clauseBLiteralsArray[k];
                                String prefixBreak = literal.substring(0, literal.indexOf('('));
                                String[] params = literal.substring(literal.indexOf('(') + 1, literal.indexOf(')')).split(",");
                                for (Map.Entry<String, String> entry : variableConstantMapping.entrySet()) {
                                    String key = entry.getKey();
                                    String value = entry.getValue();
                                    for (int m = 0; m < params.length; m++) {
                                        if (params[m].equals(key)) {
                                            params[m] = value;
                                        }
                                    }
                                }
                                literalModified2 = prefixBreak + "(" + String.join(",", params) + ")";
                                if (!literalResult.contains(literalModified2)) {
                                    literalResult.add(literalModified2);
                                }
                            }
                        }
                        String finalResult = String.join("|", literalResult);
                        resolvedClauses.add(finalResult);
                    }
                }
            }
        }
//        System.out.println("resolve " + clauseA);
//        System.out.println("resolve " + clauseB);
//        resolvedClauses.forEach(x -> {
//            if (x.equals("P(v)|T(x)|~P(v)")) {
//                System.out.println("clause a " + clauseA);
//                System.out.println("clause b " + clauseB);
//            }
//        });
        return resolvedClauses;
    }

    private static Boolean unification(String[] parametersA, String[] parametersB, Map<String, String> variableConstantMapping) {
        for (int i = 0; i < parametersA.length; i++) {
            if (!isUnificationPossible(parametersA[i].trim(), parametersB[i].trim(), variableConstantMapping)) {
                return false;
            }
        }
        return true;
    }

    private static Boolean isUnificationPossible(String paramA, String paramB, Map<String, String> variableConstantMapping) {
        if (isConstant(paramA) && isConstant(paramB)) {
            return paramA.equals(paramB);
        } else if ((isConstant(paramA) && isVariable(paramB))) {
            if (variableConstantMapping.containsKey(paramB))
                return variableConstantMapping.get(paramB).equals(paramA);
            else {
                variableConstantMapping.put(paramB, paramA);
                return true;
            }
        } else if (isVariable(paramA) && isConstant(paramB)) {
            if (variableConstantMapping.containsKey(paramA))
                return variableConstantMapping.get(paramA).equals(paramB);
            else {
                variableConstantMapping.put(paramA, paramB);
                return true;
            }
        } else if (isVariable(paramA) && isVariable(paramB)) {
            if (paramA.equals(paramB)) {
                return true;
            } else {
                variableConstantMapping.put(paramA, paramB);
                return true;
            }
        }
        return false;
    }

    private static Boolean isSameLiteral(String literalA, String literalB) {
//        System.out.println("Literal a : " + literalA);
//        System.out.println("literal b: " + literalB);
        return literalA.equals(literalB);
    }

    private static Boolean isVariable(String str) {
        if (str.charAt(0) == ' ') {
            return Character.isLowerCase(str.charAt(1));
        } else {
            return Character.isLowerCase(str.charAt(0));
        }
    }

    private static Boolean isConstant(String str) {
        if (str.charAt(0) == ' ') {
            return Character.isUpperCase(str.charAt(1));
        } else {
            return Character.isUpperCase(str.charAt(0));
        }
    }

    private static List<String> inputReader() throws IOException {
        FileReader fr = new FileReader("input.txt");
        List<String> kbList = new ArrayList<>();
        BufferedReader reader = new BufferedReader(fr);
        int querySize = Integer.parseInt(reader.readLine());
        for (int q = 0; q < querySize; q++) {
            queryList.add(reader.readLine());
        }
        int kbSize = Integer.parseInt(reader.readLine());
        for (int k = 0; k < kbSize; k++) {
            kbList.add(reader.readLine());
        }
        reader.close();
        return kbList;
    }

    private static List<String> convertToCNF(List<String> statementsList) {
        int count = 0;
        List<String> cnfList = new ArrayList<>();
        String implicationResolved = "";
        for (String statement : statementsList) {
            StringBuilder simplifiedStatement = new StringBuilder();
            for (int i = 0; i < statement.length(); i++) {
                StringBuilder c = new StringBuilder();
                while (statement.charAt(i) == '&' || statement.charAt(i) == '|' || statement.charAt(i) == '=' || statement.charAt(i) == '~') {
                    if (statement.charAt(i) == '=' && statement.charAt(i + 1) == '>') {
                        simplifiedStatement.append("=>");
                        i += 2;
                    } else {
                        simplifiedStatement.append(statement.charAt(i));
                        i++;
                    }
                }
                while (statement.charAt(i) != ')') {
                    c.append(statement.charAt(i));
                    i++;
                }
                c.append(')');
                if (count >= 0 && count <= 9) {
                    map.put("A00" + count, c.toString());
                    simplifiedStatement.append("A00").append(count);
                } else if (count >= 10 && count <= 99) {
                    map.put("A0" + count, c.toString());
                    simplifiedStatement.append("A0").append(count);
                } else if (count >= 100 && count <= 999) {
                    map.put("A" + count, c.toString());
                    simplifiedStatement.append("A").append(count);
                }
                count++;
            }
            if (statement.contains("=>")) {
                implicationResolved = removeImplies(simplifiedStatement.toString());
                cnfList.add(implicationResolved);
            } else {
                if (simplifiedStatement.charAt(0) == '~') {
                    cnfList.add("~" + map.get(String.valueOf(simplifiedStatement.substring(1))));
                } else {
                    cnfList.add(map.get(String.valueOf(simplifiedStatement)));
                }
            }
//            System.out.println(Arrays.toString(cnfList.toArray()));
        }
        return cnfList;
    }

    private static String removeImplies(String statement) {
//        System.out.println("what comes into resolveImplies " + statement);
        String left = "";
        String right = "";
        String leftResolved = "";
        String rightResolved = "";
        String output = "";
        String[] predicates = new String[2];
        String[] leftPredicates;
        predicates = statement.split("=>");
        left = predicates[0];
        right = predicates[1];
        leftPredicates = left.split("&");
        if (right.charAt(0) == '~') {
            rightResolved += "~" + map.get(right.substring(1));
        } else if (right.charAt(0) == 'A') {
            rightResolved += map.get(right);
        }
        for (int i = 0; i < leftPredicates.length - 1; i++) {
            if (leftPredicates[i].charAt(0) == '~') {
                leftResolved += map.get(leftPredicates[i].substring(1));
            } else if (leftPredicates[i].charAt(0) == 'A') {
                leftResolved += "~" + map.get(leftPredicates[i]);
            }
            leftResolved += '|';
//            System.out.println(leftPredicates[i]);
        }
        if (leftPredicates[leftPredicates.length - 1].charAt(0) == '~') {
            leftResolved += map.get(leftPredicates[leftPredicates.length - 1].substring(1));
        } else if (leftPredicates[leftPredicates.length - 1].charAt(0) == 'A') {
            leftResolved += "~" + map.get(leftPredicates[leftPredicates.length - 1]);
        }
        output = leftResolved + "|" + rightResolved;
        return output;
    }

    private static String removeSpace(String str) {
        String[] trimmedArray = str.split(" ");
        String output = "";
        for (int i = 0; i < trimmedArray.length; i++) {
            output += trimmedArray[i];
        }
        return output;
    }
}