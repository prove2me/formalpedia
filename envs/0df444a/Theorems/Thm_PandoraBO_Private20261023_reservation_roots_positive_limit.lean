-- Prove2me | Theorems.Thm_PandoraBO_Private20261023_reservation_roots_positive_limit
-- name    : PandoraBO.Private20261023.reservation_roots_positive_limit
-- status  : Proved
-- author  : @QianJaneXie
-- created : 2026-10-24T01:16:02.713125+00:00
-- url     : https://prove2.me/theorems/5a25eb9f-32e3-4bad-abf8-b8573f568a0e
-- title:
--   Reservation roots are continuous at positive multipliers
-- statement:
--   For a sequence of positive multipliers tending to a positive limit, the unique reservation roots converge to the reservation root at that limit. No monotonicity, bounded support, continuity of the reward law, or atomlessness is assumed.
-- source:
--   Auxiliary lemma for Xie et al., author revised manuscript reviewed 23 October 2026, Appendix B.5 and the finite independent-box policy model.

import Definitions.Def_PandoraBO_Model
open MeasureTheory Filter
open scoped Topology
set_option autoImplicit false

theorem PandoraBO.Private20261023.reservation_roots_positive_limit {n : ℕ} (M : PandoraBO.Instance n) (i : PandoraBO.Box n)
    (multipliers : ℕ → ℝ) (limit : ℝ)
    (hpos : ∀ k, 0 < multipliers k) (hlimitpos : 0 < limit)
    (hlim : Tendsto multipliers atTop (nhds limit)) :
    ∃ roots : ℕ → ℝ, ∃ root : ℝ,
      (∀ k, PandoraBO.reservationRoot M i (multipliers k * M.cost i) (roots k)) ∧
      PandoraBO.reservationRoot M i (limit * M.cost i) root ∧
      Tendsto roots atTop (nhds root)  := by sorry
