-- Prove2me | Theorems.Thm_SetCoverThreshold_MaxCover_prop_2_1_2
-- name    : SetCoverThreshold.MaxCover.prop_2_1_2
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-09-27T13:03:32.54114+00:00
-- url     : https://prove2.me/theorems/9599c73f-0ef0-42bf-b730-cf06a8b76fd6
-- title:
--   Proposition 2.1.2 — gap NP-hardness of MAX 3SAT-5 (from Theorem 2.1.1)
-- statement:
--   Assume the cited Theorem 2.1.1: for some bound $B$ and some $\varepsilon_0>0$ it is NP-hard to distinguish satisfiable 3CNF-B formulas from 3CNF-B formulas in which at most a $(1-\varepsilon_0)$-fraction of the clauses can be satisfied simultaneously. Then there is $\varepsilon>0$ such that it is NP-hard to distinguish
--   $$\{\text{satisfiable 3CNF-5 formulas}\}\quad\text{from}\quad\{\text{3CNF-5 formulas with at most a }(1-\varepsilon)\text{-fraction of clauses simultaneously satisfiable}\}.$$
--   That is, every NP language maps in polynomial time to satisfiable 3CNF-5 formulas on its members and to 3CNF-5 formulas with at most a $(1-\varepsilon)$-fraction satisfiable on its non-members.
--
--   This is the starting point of all of Feige's reductions: the regular structure of 3CNF-5 formulas makes the questions of the proof system uniformly distributed.
--
--   **Formalization Note** Theorem 2.1.1 is a cited result and enters as the hypothesis `Thm211`. Formulas are encoded by Cook's CNF encoding. The "no" formulas are required to have at least one clause (`F ≠ []`), since the empty formula is satisfiable and would otherwise belong to both classes, making the distinction trivial.
-- source:
--   Feige, A threshold of ln n for approximating set cover, J. ACM 45(4) (1998), p. 640, Proposition 2.1.2

import Mathlib
import Definitions.Def_CookPvsNP_defs
import Definitions.Def_SetCoverThreshold_MaxCover_Formula

namespace SetCoverThreshold.MaxCover

open CookPvsNP

/-- **Proposition 2.1.2** (Feige 1998, p. 640), from the cited Theorem 2.1.1: for some `ε > 0`
it is NP-hard to distinguish satisfiable 3CNF-5 formulas from 3CNF-5 formulas in which at most a
`(1 − ε)`-fraction of the clauses can be satisfied simultaneously (the latter having at least one
clause, so that the two classes are disjoint). -/
theorem prop_2_1_2 (h211 : Thm211) :
    ∃ ε : ℝ, 0 < ε ∧
      GapNPHard encodeCNF (fun F => Is3CNF5 F ∧ F.Satisfiable)
        (fun F => Is3CNF5 F ∧ F ≠ [] ∧ AtMostFracSat (1 - ε) F) := by sorry

end SetCoverThreshold.MaxCover
