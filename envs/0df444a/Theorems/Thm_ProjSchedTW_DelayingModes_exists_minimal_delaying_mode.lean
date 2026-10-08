-- Prove2me | Theorems.Thm_ProjSchedTW_DelayingModes_exists_minimal_delaying_mode
-- name    : ProjSchedTW.DelayingModes.exists_minimal_delaying_mode
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-03T22:41:01.029024+00:00
-- url     : https://prove2.me/theorems/c80bcb20-ad47-4bb5-b62c-fcb9cbd77a86
-- title:
--   Theorem 2.5.7 — every feasible schedule obeys a minimal delaying mode of each forbidden set
-- statement:
--   Let $F$ be a forbidden set of a project, i.e. $\sum_{i\in F}r_{ik}>R_k$ for some resource $k$. For every feasible schedule $S$ (time-feasible and resource-feasible) there is a minimal delaying mode $(i,B)$ for $F$ — $B$ is a minimal delaying alternative for $F$ and $i\in F\setminus B$ — such that
--   $$S_j\ge S_i+p_i\qquad(j\in B).\qquad(2.5.4)$$
--
--   Thus every feasible schedule resolves the conflict of $F$ by letting one fixed activity $i$ of $F$ complete before all activities of a minimal delaying alternative start. This is the completeness statement behind the enumeration scheme of De Reyck and Herroelen (Algorithm 2.5.8): branching over the minimal delaying modes of a forbidden active set loses no feasible schedule. Since the objective function plays no role, the result holds for every objective.
--
--   **Formalization Note.** The standing assumptions of the model are hypotheses; resource constraints are required for all $t\ge0$. $F$ is an arbitrary forbidden set, not necessarily minimal; $B$ must be minimal and $i\notin B$.
-- source:
--   Neumann, Schwindt & Zimmermann, Project Scheduling with Time Windows and Scarce Resources, 2nd ed., Springer 2003, p. 49, Theorem 2.5.7, Eq. (2.5.4)

import Mathlib
import Definitions.Def_ProjSchedTW_DelayingModes_Project

namespace ProjSchedTW.DelayingModes

theorem exists_minimal_delaying_mode {n : ℕ} {K : Type} [Fintype K] (P : Project n K)
    (hP : P.StandingAssumptions) (F : Finset (Fin (n + 2))) (hF : P.IsForbidden F)
    (S : Fin (n + 2) → ℝ) (hS : P.IsFeasible S) :
    ∃ (i : Fin (n + 2)) (B : Finset (Fin (n + 2))),
      P.IsMinimalDelayingMode F i B ∧ ∀ j ∈ B, S i + P.p i ≤ S j := by sorry

end ProjSchedTW.DelayingModes
