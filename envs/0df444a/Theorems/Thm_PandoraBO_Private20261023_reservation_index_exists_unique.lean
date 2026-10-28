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
--   This supplies the index used by every policy target. It requires strict decrease only where expected improvement is positive.
-- source:
--   Qian Xie, Raul Astudillo, Peter I. Frazier, Ziv Scully, and Alexander Terenin. [Cost-aware Bayesian Optimization via the Pandora's Box Gittins Index](https://arxiv.org/abs/2406.20062). NeurIPS 2024. Section 3.2, equation (5): existence and uniqueness of the positive-cost reservation index.

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
