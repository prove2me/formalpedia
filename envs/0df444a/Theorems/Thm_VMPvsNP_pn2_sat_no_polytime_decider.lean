-- Prove2me | Theorems.Thm_VMPvsNP_pn2_sat_no_polytime_decider
-- name    : VMPvsNP.pn2_sat_no_polytime_decider
-- status  : Open
-- author  : @hao jia
-- created : 2026-10-08T04:44:43.411982+00:00
-- url     : https://prove2.me/theorems/65d31003-4fb1-4888-8871-d7d073272b02
-- title:
--   Every total polynomial-time SAT-CNF candidate has an error input
-- statement:
--   Does every total uniformly polynomial-time Boolean-answering deterministic multitape machine have an input on which it gives the wrong SAT-CNF answer?
--
--   Let L be the shared binary SAT-CNF language, including rejection of malformed encodings. Let H(M,y,t,b) denote actual local execution halting by t transitions with Boolean answer b. For every machine M and positive integers c and k, the target is
--
--   $$\left(\forall y\in\{0,1\}^*\;\exists b\in\{\mathrm{false},\mathrm{true}\},\ H(M,y,c\max(1,|y|)^k,b)\right)\Longrightarrow\left(\exists x\in\{0,1\}^*\;\exists b\in\{\mathrm{false},\mathrm{true}\},\ H(M,x,c\max(1,|x|)^k,b)\land\neg(b=\mathrm{true}\iff x\in L)\right).$$
--
--   Total bounded halting is a premise, but correctness and assumed failure are not. The error input may depend on M, c, and k; one common witness for every candidate is not required. A failure of one algorithm or a restricted model does not settle this universal target.
--
--   **Formalization Note** PA and PN2 import the same published definitions. This is an OPEN root statement with an explicit proof placeholder, not a root proof or an admitted P-versus-NP conclusion. The concrete representation correspondence remains subject to faithfulness review.
-- source:
--   Stephen Cook, The Complexity of Theorem-Proving Procedures, STOC 1971, pp. 151-158, https://doi.org/10.1145/800157.805047; Clay Mathematics Institute, P vs NP Problem, https://www.claymath.org/millennium/p-vs-np/ . This item states the uniform SAT-CNF root question in the shared explicit model; it is not a theorem asserted to have been proved by those sources.

import Definitions.Def_VMPvsNP_SATModel

theorem VMPvsNP.pn2_sat_no_polytime_decider :
    ∀ M : VMPvsNP.Machine, ∀ c k : Nat,
      0 < c → 0 < k →
      (∀ y : List Bool, ∃ answer : Bool,
        VMPvsNP.HaltsWithin M y (VMPvsNP.polynomialBound c k y) answer) →
      ∃ x : List Bool, ∃ answer : Bool,
        VMPvsNP.HaltsWithin M x (VMPvsNP.polynomialBound c k x) answer ∧
        ¬ (answer = true ↔ VMPvsNP.SATCNF x) := by sorry
