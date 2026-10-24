-- Prove2me | Theorems.Thm_PandoraBO_Private20261023_reservation_roots_zero_limit
-- name    : PandoraBO.Private20261023.reservation_roots_zero_limit
-- status  : Proved
-- author  : @QianJaneXie
-- created : 2026-10-24T01:05:36.159862+00:00
-- url     : https://prove2.me/theorems/53b25ef7-4103-4f53-916b-d52000188125
-- title:
--   Reservation roots converge to the essential supremum at zero cost
-- statement:
--   For each integrable box reward, expected improvement at a real threshold is zero exactly when the reward is almost surely below that threshold, and it is positive exactly when the threshold is below the extended-real essential supremum. For every sequence of strictly positive cost multipliers tending to zero, the corresponding finite reservation roots exist and converge in the extended real line to that essential supremum. The multiplier sequence need not be monotone, and the reward may have bounded or unbounded support and atoms.
-- source:
--   Xie et al., author revised manuscript reviewed 23 October 2026, Appendix B.5, Lemma 7 Part I, discussion of equation (43) and the zero-multiplier limit, p. 21. The sequence conclusion here does not require the monotonicity used elsewhere in the policy argument.

import Definitions.Def_PandoraBO_Model
import Mathlib.MeasureTheory.Function.EssSup
import Mathlib.Topology.Instances.EReal.Lemmas
open MeasureTheory Filter
open scoped Topology
set_option autoImplicit false

theorem PandoraBO.Private20261023.reservation_roots_zero_limit {n : ℕ} (M : PandoraBO.Instance n) (i : PandoraBO.Box n) :
    (∀ z : ℝ, PandoraBO.expectedImprovement M i z = 0 ↔ ∀ᵐ y ∂M.law i, y ≤ z) ∧
    (∀ z : ℝ, 0 < PandoraBO.expectedImprovement M i z ↔
      (z : EReal) < PandoraBO.zeroReservationIndex M i) ∧
    ∀ multipliers : ℕ → ℝ, (∀ k, 0 < multipliers k) →
      Tendsto multipliers atTop (nhds 0) → ∃ roots : ℕ → ℝ,
        (∀ k, PandoraBO.reservationRoot M i (multipliers k * M.cost i) (roots k)) ∧
        Tendsto (fun k => (roots k : EReal)) atTop (nhds (PandoraBO.zeroReservationIndex M i)) := by sorry
