-- Prove2me | Theorems.Thm_SupplyChainTheory_vrp_tsp_bounds
-- name    : SupplyChainTheory.vrp_tsp_bounds
-- status  : Proved
-- author  : @naimengye
-- created : 2026-09-24T01:05:02.475263+00:00
-- url     : https://prove2.me/theorems/4922f7ab-0799-4674-b5d4-c547c83068b0
-- title:
--   Theorem 11.6 (Haimovich and Rinnooy Kan): $\max\{2\frac{n}{C}\bar c, z_T\} \le z^* \le 2\lceil n/C\rceil\bar c + (1 - \frac{1}{C}) z_T$
-- statement:
--   **Theorem 11.6.** For a VRP instance on nodes $N = \{0, 1, \dots, n\}$ with metric distances,
--   $d_i = 1$ for every customer, vehicle capacity $C \ge 1$ and an unrestricted number of vehicles,
--
--   $$ \max\Big\{2\frac{n}{C}\bar c,\ z_T\Big\} \;\le\; z^* \;\le\; 2\Big\lceil\frac{n}{C}\Big\rceil\bar c + \Big(1 - \frac{1}{C}\Big)z_T, $$
--
--   where $z^*$ is the optimal VRP objective, $z_T$ the length of the optimal TSP tour through all
--   the nodes, and $\bar c = \frac{1}{n}\sum_{i=1}^n c_{0i}$ the average distance from the depot to
--   the customers. The lower bound combines the radial bound on each route with $z_T \le z^*$; the
--   upper bound is the iterated optimal tour partition heuristic applied to the optimal tour, using
--   $\lceil n/C\rceil/n \ge 1/C$. Both bounds are tight (Problem 11.18); the first term of the upper
--   bound is the radial distance to the customers and the second the local delivery distance, and
--   as $C \to \infty$ both bounds approach $z_T$.
-- source:
--   Lawrence V. Snyder and Zuo-Jun Max Shen, Fundamentals of Supply Chain Theory, 2nd ed., Wiley 2019, DOI 10.1002/9781119584445, pp. 495-496, Sect. 11.4.1, Theorem 11.6, Eq. (11.57), and its proof; after Haimovich and Rinnooy Kan (1985)

import Definitions.Def_SupplyChainTheory_vrp

namespace SupplyChainTheory

theorem vrp_tsp_bounds {n : ℕ} (c : Fin (n + 1) → Fin (n + 1) → ℝ) (hc : VRPMetric c)
    (hn : 1 ≤ n) (C : ℕ) (hC : 1 ≤ C) :
    max (2 * ((n : ℝ) / C) * avgDepotDist c) (tspOpt c) ≤ vrpOpt c C
      ∧ vrpOpt c C ≤ 2 * ⌈(n : ℝ) / C⌉₊ * avgDepotDist c + (1 - 1 / (C : ℝ)) * tspOpt c := by sorry

end SupplyChainTheory
