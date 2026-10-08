-- Prove2me | Theorems.Thm_ProjSchedTW_StableSchedules_uniform_shifts_suffice
-- name    : ProjSchedTW.StableSchedules.uniform_shifts_suffice
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-04T01:14:33.889503+00:00
-- url     : https://prove2.me/theorems/11d2faa6-9471-40da-9c28-9ea5bda8cd60
-- title:
--   Lemma 3.2.4 — order-preserving and order-monotone shifts may be taken uniform
-- statement:
--   Let $S$ be a feasible schedule of a project. Then:
--
--   1. there is an order-preserving left-shift from $S$ if and only if there is a uniform order-preserving left-shift from $S$;
--   2. there is an order-monotone left-shift from $S$ if and only if there is a uniform order-monotone left-shift from $S$;
--   3. there is a pair of opposite order-preserving shifts from $S$ if and only if there is a pair of opposite uniform order-preserving shifts from $S$;
--   4. there is a pair of opposite order-monotone shifts from $S$ if and only if there is a pair of opposite uniform order-monotone shifts from $S$.
--
--   Here a shift from $S$ to $S'$ is uniform if
--   $$S'-S=\lambda z,\qquad z\in\{0,1\}^{n+2},\ \lambda\neq 0,$$
--   so every moved activity moves by the same amount.
--
--   The lemma lets later arguments consider only shifts that move a set of activities rigidly by a common amount.
-- source:
--   Neumann, Schwindt & Zimmermann, Project Scheduling with Time Windows and Scarce Resources, 2nd ed., Springer 2003, p. 209, Lemma 3.2.4

import Mathlib
import Definitions.Def_ProjSchedTW_StableSchedules_Project
import Definitions.Def_ProjSchedTW_StableSchedules_Shifts

namespace ProjSchedTW.StableSchedules

/-- Lemma 3.2.4 (p. 209). For a feasible schedule `S`: there is an order-preserving
(order-monotone) left-shift from `S` iff there is a uniform one; and there is a pair of opposite
order-preserving (order-monotone) shifts from `S` iff there is a pair of opposite uniform
order-preserving (order-monotone) shifts from `S`. -/
theorem uniform_shifts_suffice {n : ℕ} {K : Type} (P : Project n K) (S : Fin (n + 2) → ℝ)
    (hS : S ∈ feasibleSet P) :
    ((∃ S', IsOrderPreservingShift P S S' ∧ ProjSchedTW.ActiveSchedules.IsLeftShift S S') ↔
      (∃ S', IsOrderPreservingShift P S S' ∧ ProjSchedTW.ActiveSchedules.IsLeftShift S S' ∧ IsUniformShift S S')) ∧
    ((∃ S', IsOrderMonotoneShift P S S' ∧ ProjSchedTW.ActiveSchedules.IsLeftShift S S') ↔
      (∃ S', IsOrderMonotoneShift P S S' ∧ ProjSchedTW.ActiveSchedules.IsLeftShift S S' ∧ IsUniformShift S S')) ∧
    ((∃ S' S'', IsOrderPreservingShift P S S' ∧ IsOrderPreservingShift P S S'' ∧
        AreOpposite S S' S'') ↔
      (∃ S' S'', IsOrderPreservingShift P S S' ∧ IsOrderPreservingShift P S S'' ∧
        IsUniformShift S S' ∧ IsUniformShift S S'' ∧ AreOpposite S S' S'')) ∧
    ((∃ S' S'', IsOrderMonotoneShift P S S' ∧ IsOrderMonotoneShift P S S'' ∧
        AreOpposite S S' S'') ↔
      (∃ S' S'', IsOrderMonotoneShift P S S' ∧ IsOrderMonotoneShift P S S'' ∧
        IsUniformShift S S' ∧ IsUniformShift S S'' ∧ AreOpposite S S' S'')) := by sorry

end ProjSchedTW.StableSchedules
