-- Prove2me | Theorems.Thm_SupplyChainTheory_vrp_radial_bound
-- name    : SupplyChainTheory.vrp_radial_bound
-- status  : Proved
-- author  : @naimengye
-- created : 2026-09-24T01:03:10.809724+00:00
-- url     : https://prove2.me/theorems/7709b2db-d4cf-4e10-ad7d-8a42bb9ae06c
-- title:
--   Theorem 11.6, lower bound (radial part): $2\frac{n}{C}\bar c \le z^*$
-- statement:
--   For a unit-demand VRP instance on $n \ge 1$ customers with capacity $C \ge 1$ and metric
--   distances, $2\frac{n}{C}\bar c \le z^*$, where $\bar c$ is the average distance from the depot to
--   the customers. Each route serving the customer set $N_k$ has length at least
--   $2\max_{i \in N_k} c_{0i}$ by the triangle inequality, hence at least
--   $2\sum_{i \in N_k} c_{0i}/|N_k| \ge 2\sum_{i \in N_k} c_{0i}/C$, and summing over the routes gives
--   the bound. The radial term dominates for large $n$ (Theorem 11.7).
-- source:
--   Lawrence V. Snyder and Zuo-Jun Max Shen, Fundamentals of Supply Chain Theory, 2nd ed., Wiley 2019, DOI 10.1002/9781119584445, p. 495, Sect. 11.4.1, the proof of Theorem 11.6 ('We prove the lower bound first')

import Definitions.Def_SupplyChainTheory_vrp

namespace SupplyChainTheory

theorem vrp_radial_bound {n : ℕ} (c : Fin (n + 1) → Fin (n + 1) → ℝ) (hc : VRPMetric c)
    (hn : 1 ≤ n) (C : ℕ) (hC : 1 ≤ C) :
    2 * ((n : ℝ) / C) * avgDepotDist c ≤ vrpOpt c C := by sorry

end SupplyChainTheory
