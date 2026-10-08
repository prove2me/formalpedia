-- Prove2me | Theorems.Thm_ProjSchedTW_StableSchedules_opposite_monotone_iff_order_segment
-- name    : ProjSchedTW.StableSchedules.opposite_monotone_iff_order_segment
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-04T01:14:54.172614+00:00
-- url     : https://prove2.me/theorems/32ac5185-2b4c-4176-b24b-55e9f6121d6d
-- title:
--   Lemma 3.2.9 — opposite order-monotone shifts exist iff S is interior to a segment inside one order polytope
-- statement:
--   Let $S$ be a feasible schedule. There is a pair of opposite order-monotone shifts from $S$ if and only if there are:
--
--   1. a feasible strict order $O\subseteq O(S)$, and
--   2. schedules $S'\neq S$ and $S''\neq S$ in the order polytope $\mathcal S_T(O)$, that is, time-feasible with $O\subseteq O(S')$ and $O\subseteq O(S'')$,
--
--   such that $S$ lies on the line segment joining $S'$ and $S''$:
--   $$S\in[S',S''],\qquad S',S''\in\mathcal S_T(O),\quad O\subseteq O(S),\ O\text{ feasible}.$$
--
--   In words, if $S$ is not a local extreme point of $\mathcal S$, a segment through $S$ can be chosen inside a single order polytope. This is the step of Theorem 3.2.10(d) that uses convexity of order polytopes.
--
--   **Formalization Note** The book says that $O$ "represents a subset of some orders $O(S')$ and $O(S'')$". This is formalized as $S',S''\in\mathcal S_T(O)$, following the sentence before the lemma ("this line segment can be chosen such that it is included in an order polytope $\mathcal S_T(O)$ with $O\subseteq O(S)$"). The book gives no proof and cites Neumann, Nübel and Schwindt (2000), *Active and stable project scheduling*, Math. Methods Oper. Res. 52.
-- source:
--   Neumann, Schwindt & Zimmermann, Project Scheduling with Time Windows and Scarce Resources, 2nd ed., Springer 2003, p. 211, Lemma 3.2.9 (proof cited to Neumann et al. 2000)

import Mathlib
import Definitions.Def_ProjSchedTW_StableSchedules_Project
import Definitions.Def_ProjSchedTW_StableSchedules_Shifts

namespace ProjSchedTW.StableSchedules

/-- Lemma 3.2.9 (p. 211). For a feasible schedule `S`: there is a pair of opposite
order-monotone shifts from `S` iff there is a feasible strict order `O ⊆ O(S)` and schedules
`S' ≠ S`, `S'' ≠ S` in the order polytope `S_T(O)` (time-feasible with `O ⊆ O(S')`,
`O ⊆ O(S'')`) such that `S` lies on the line segment joining `S'` and `S''`. -/
theorem opposite_monotone_iff_order_segment {n : ℕ} {K : Type} (P : Project n K)
    (S : Fin (n + 2) → ℝ) (hS : S ∈ feasibleSet P) :
    (∃ S' S'', IsOrderMonotoneShift P S S' ∧ IsOrderMonotoneShift P S S'' ∧
        AreOpposite S S' S'') ↔
      ∃ O : Set (Fin (n + 2) × Fin (n + 2)), IsFeasibleOrder P O ∧ O ⊆ scheduleOrder P S ∧
        ∃ S' S'' : Fin (n + 2) → ℝ,
          S' ∈ timeFeasibleSet P ∧ S'' ∈ timeFeasibleSet P ∧
          O ⊆ scheduleOrder P S' ∧ O ⊆ scheduleOrder P S'' ∧
          S' ≠ S ∧ S'' ≠ S ∧ S ∈ segment ℝ S' S'' := by sorry

end ProjSchedTW.StableSchedules
