-- Prove2me | Theorems.Thm_SchedComplexity_OneMachine_theorem_4_bcef_knapsack_reducible
-- name    : SchedComplexity.OneMachine.theorem_4_bcef_knapsack_reducible
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-06T04:50:57.547045+00:00
-- url     : https://prove2.me/theorems/a0d8a6eb-d22f-4b3b-8fa1-8049d33e16cb
-- title:
--   Theorem 4(b),(c),(e),(f) — KNAPSACK reduces to four single-machine problems
-- statement:
--   Theorem 4 of Brucker, Lenstra and Rinnooy Kan states that KNAPSACK is reducible to ten scheduling problems. This item formalizes parts (b), (c), (e) and (f), the single-machine problems with due dates:
--
--   $$\mathsf{KNAPSACK}\ \le_p\ n|1|L_{\max}\le0|\textstyle\sum w_jC_j,\qquad \mathsf{KNAPSACK}\ \le_p\ n|1|r_n\ge0|L_{\max},$$
--   $$\mathsf{KNAPSACK}\ \le_p\ n|1||\textstyle\sum w_jU_j,\qquad \mathsf{KNAPSACK}\ \le_p\ n|1|r_n\ge0,w_j=1|\textstyle\sum w_jU_j .$$
--
--   Here $\le_p$ is polynomial-time many-one reducibility of languages (Karp; Cook's Definition 3): a function on strings, computable by a one-tape Turing machine in polynomial time, maps codes of KNAPSACK yes-instances (positive integers $a_1,\dots,a_t,b$ with a subset summing to $b$) into the target language and every other string outside it. The target languages are the recognition versions "is there a feasible schedule of value $\le y$?" of the four problems, with instances restricted to the problem class. Together with the NP-completeness of KNAPSACK (Theorem 2(b)) the reductions show that the four problems are NP-hard. Parts (a), (d) and (g)–(j) are the subject of other missions in this series.
--
--   **Formalization Note** The paper's "reducible" (Section 2, p. 4: an instance of the target "can be constructed in polynomial time such that solving the instance of P will solve the instance of P' as well") is read as Karp reducibility, `CookPvsNP.PolyReducible`, over the alphabet `BSym` with binary number codes. The reduction must handle every string, including codes of KNAPSACK instances with $b\ge A$ (excluded in the proof by "We may assume that $0<b<A$") and strings that are not codes at all.
-- source:
--   Brucker, Lenstra & Rinnooy Kan, Complexity of Machine Scheduling Problems, Mathematisch Centrum Report BW 43/75 (1975), p. 16, Theorem 4(b),(c),(e),(f); constructions pp. 17, 19

import Mathlib
import Definitions.Def_SchedComplexity_OneMachine_Knapsack
import Definitions.Def_SchedComplexity_OneMachine_Problems

namespace SchedComplexity.OneMachine

open CookPvsNP

/-- Theorem 4(b), (c), (e), (f) (Brucker, Lenstra & Rinnooy Kan, Report BW 43/75, p. 16): KNAPSACK
(over positive integers) is polynomial-time many-one reducible to each of the single-machine
problems `n|1|L_max≤0|∑w_jC_j`, `n|1|r_n≥0|L_max`, `n|1||∑w_jU_j` and
`n|1|r_n≥0,w_j=1|∑w_jU_j`, all languages over the binary alphabet `BSym`. -/
theorem theorem_4_bcef_knapsack_reducible :
    PolyReducible knapsackLang langLmaxSumWC ∧
    PolyReducible knapsackLang langRnLmax ∧
    PolyReducible knapsackLang langSumWU ∧
    PolyReducible knapsackLang langRnUnitSumWU := by sorry

end SchedComplexity.OneMachine
