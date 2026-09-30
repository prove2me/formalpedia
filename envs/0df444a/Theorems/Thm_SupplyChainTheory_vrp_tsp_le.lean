-- Prove2me | Theorems.Thm_SupplyChainTheory_vrp_tsp_le
-- name    : SupplyChainTheory.vrp_tsp_le
-- status  : Proved
-- author  : @naimengye
-- created : 2026-09-24T01:03:59.303988+00:00
-- url     : https://prove2.me/theorems/b135053f-ec3d-45bd-8680-90aee1058f99
-- title:
--   Theorem 11.6, lower bound (routing part): $z_T \le z^*$
-- statement:
--   For a unit-demand VRP instance with metric distances, $z_T \le z^*$: the optimal TSP tour
--   through the depot and all customers is no longer than the optimal VRP solution. Concatenating
--   the routes of a VRP solution gives a closed walk through all nodes that visits the depot once
--   per route; shortcutting the repeated depot visits, by the triangle inequality, yields a tour no
--   longer than the solution. As $C \to \infty$ this bound and the upper bound of Theorem 11.6 both
--   approach $z_T$.
-- source:
--   Lawrence V. Snyder and Zuo-Jun Max Shen, Fundamentals of Supply Chain Theory, 2nd ed., Wiley 2019, DOI 10.1002/9781119584445, p. 495, Sect. 11.4.1, the proof of Theorem 11.6 ('Moreover, by the triangle inequality, zT ≤ z∗')

import Definitions.Def_SupplyChainTheory_vrp

namespace SupplyChainTheory

theorem vrp_tsp_le {n : ℕ} (c : Fin (n + 1) → Fin (n + 1) → ℝ) (hc : VRPMetric c)
    (hn : 1 ≤ n) (C : ℕ) (hC : 1 ≤ C) : tspOpt c ≤ vrpOpt c C := by sorry

end SupplyChainTheory
