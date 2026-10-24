-- Prove2me | Theorems.Thm_PandoraBO_Private20261023_reservation_roots_strict_antitone
-- name    : PandoraBO.Private20261023.reservation_roots_strict_antitone
-- status  : Proved
-- author  : @QianJaneXie
-- created : 2026-10-24T00:54:28.467633+00:00
-- url     : https://prove2.me/theorems/0997a7b4-4e49-4f41-b619-8fe060648815
-- title:
--   Reservation roots strictly decrease with the cost multiplier
-- statement:
--   Fix a box with positive opening cost. Suppose z and w solve the reservation-root equations at respective real multipliers s<t. Then w<z. The statement assumes the two displayed roots, without a separate assertion that roots exist at every real multiplier.
-- source:
--   Supporting monotonicity argument in Xie et al., author revised manuscript reviewed 23 October 2026, Appendix B.5, proof of Lemma 7 (equation (43) and the final subsequence argument on page 22). Isolated algebraic/analytic auxiliary lemma for formalization.

import Definitions.Def_PandoraBO_Model
open PandoraBO
set_option autoImplicit false

theorem PandoraBO.Private20261023.reservation_roots_strict_antitone {n : ℕ} (M : Instance n) (i : Box n) (s t z w : ℝ)
    (hst : s < t)
    (hz : reservationRoot M i (s * M.cost i) z)
    (hw : reservationRoot M i (t * M.cost i) w) :
    w < z := by sorry
