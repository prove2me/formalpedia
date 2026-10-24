-- Prove2me | Theorems.Thm_PandoraBO_Private20261023_reservation_index_exists_unique
-- name    : PandoraBO.Private20261023.reservation_index_exists_unique
-- status  : Proved
-- author  : @QianJaneXie
-- created : 2026-10-23T23:42:13.928532+00:00
-- url     : https://prove2.me/theorems/83352034-b8cb-409f-b52f-d71f796d9149
-- title:
--   Equation (5) — existence and uniqueness of the reservation index
-- statement:
--   For an integrable real reward $F_i$, positive deterministic inspection cost $c_i$, and any $\lambda>0$, there exists a unique finite real number $g_i$ such that
--
--   $$\mathbb E[(F_i-g_i)_+]=\lambda c_i.$$
--
--   This supplies the index used by every policy target. It requires strict decrease only where expected improvement is positive, rather than the incorrect assertion that expected improvement is strictly decreasing everywhere for bounded rewards.
-- source:
--   Private proof development for Section 3.2, equation (5), of Xie et al., Cost-aware Bayesian Optimization via the Pandora's Box Gittins Index; author-revised manuscript reviewed on 23 October 2026. The positive-cost reservation-index statement is unchanged from arXiv:2406.20062v3. Mission source version: the author-revised manuscript reviewed on 23 October 2026, intended for arXiv v4; public posting is pending. References to arXiv v3 identify the earlier published version.

import Definitions.Def_PandoraBO_Model
import Mathlib.Algebra.Order.Group.MinMax
import Mathlib.Topology.MetricSpace.Lipschitz
import Mathlib.MeasureTheory.Integral.DominatedConvergence
import Mathlib.Topology.Order.IntermediateValue

set_option autoImplicit false

namespace PandoraBO.Private20261023

theorem reservation_index_exists_unique {n : ℕ} (M : Instance n)
    (multiplier : ℝ) (hpos : 0 < multiplier) (i : Box n) :
    ∃! z : ℝ, reservationRoot M i (multiplier * M.cost i) z := by sorry

end PandoraBO.Private20261023
