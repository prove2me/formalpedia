-- Prove2me | Theorems.Thm_SchedComplexity_Shops_theorem_4_ghij_knapsack_reducible
-- name    : SchedComplexity.Shops.theorem_4_ghij_knapsack_reducible
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-06T14:44:37.886811+00:00
-- url     : https://prove2.me/theorems/0174387d-8479-4750-adfa-724445cf0b04
-- title:
--   Theorem 4(g)–(j) — KNAPSACK reduces to two flow-shop and two job-shop makespan problems
-- statement:
--   Theorem 4 of the report reads: *KNAPSACK is reducible to the following problems:* (a) $n|1|r_n{\ge}0,w_j{=}1|\sum w_jC_j$; (b) $n|1|L_{\max}{\le}0|\sum w_jC_j$; (c) $n|1|r_n{\ge}0|L_{\max}$; (d) $n|1||\sum w_jT_j$; (e) $n|1||\sum w_jU_j$; (f) $n|1|r_n{\ge}0,w_j{=}1|\sum w_jU_j$; (g) $n|2|F,r_n{\ge}0|C_{\max}$; (h) $n|2|F,\mathit{tree}|C_{\max}$; (i) $n|2|G,m_j{\le}3|C_{\max}$; (j) $n|3|G,m_j{\le}2|C_{\max}$. Only parts (g)–(j) are formalized here.
--
--   Write $L_{\mathrm{KS}}$ for the language of binary codes of KNAPSACK yes-instances with positive data, and $L_g, L_h, L_i, L_j$ for the languages of the four recognition problems (instance in the class and a feasible schedule with $C_{\max}\le y$). The theorem states
--
--   $$L_{\mathrm{KS}}\le_p L_g,\qquad L_{\mathrm{KS}}\le_p L_h,\qquad L_{\mathrm{KS}}\le_p L_i,\qquad L_{\mathrm{KS}}\le_p L_j,$$
--
--   where $\le_p$ is polynomial-time many-one reducibility: a function computable in polynomial time by a Turing machine maps every string $x$ to a string $f(x)$ with $x\in L_{\mathrm{KS}}\iff f(x)\in L_\ast$.
--
--   Together with the NP-completeness of KNAPSACK, this shows that minimizing the makespan is NP-hard already in the two-machine flow shop with one nonzero release date or with tree-like precedence constraints, and in job shops with two machines and at most three operations per job or three machines and at most two operations per job.
--
--   **Formalization Note** "Reducible" (Section 2, p. 4) is read as Karp reducibility, `CookPvsNP.PolyReducible` from the published definitions `CookPvsNP_defs`. Strings are over the four-letter alphabet of `ProjSchedTW.Complexity.Encoding`, with every number in binary. Membership in NP is not part of the statement.
-- source:
--   Brucker, Lenstra & Rinnooy Kan, Complexity of Machine Scheduling Problems, Mathematisch Centrum Report BW 43/75 (1975), p. 16, Theorem 4(g), (h), (i), (j); proofs pp. 16–18

import Mathlib
import Definitions.Def_SchedComplexity_OneMachine_Knapsack
import Definitions.Def_SchedComplexity_Shops_Problems

namespace SchedComplexity.Shops

open CookPvsNP

/-- Theorem 4(g), (h), (i), (j), Brucker, Lenstra & Rinnooy Kan, Report BW 43/75, p. 16: KNAPSACK
is polynomial-time many-one reducible to each of `n|2|F,r_n≥0|C_max`, `n|2|F,tree|C_max`,
`n|2|G,m_j≤3|C_max` and `n|3|G,m_j≤2|C_max`. -/
theorem theorem_4_ghij_knapsack_reducible :
    PolyReducible SchedComplexity.OneMachine.knapsackLang langFlowRn ∧ PolyReducible SchedComplexity.OneMachine.knapsackLang langFlowTree ∧
    PolyReducible SchedComplexity.OneMachine.knapsackLang langJob2Ops3 ∧ PolyReducible SchedComplexity.OneMachine.knapsackLang langJob3Ops2 := by sorry

end SchedComplexity.Shops
