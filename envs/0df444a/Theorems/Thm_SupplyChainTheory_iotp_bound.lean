-- Prove2me | Theorems.Thm_SupplyChainTheory_iotp_bound
-- name    : SupplyChainTheory.iotp_bound
-- status  : Proved
-- author  : @naimengye
-- created : 2026-09-24T01:04:33.650987+00:00
-- url     : https://prove2.me/theorems/189bde3d-e61c-4788-b64a-7693d6e7f3e9
-- title:
--   Eq. (11.59), the iterated optimal tour partition bound: for every customer tour some partition into consecutive routes costs at most $2\ell\bar c + (1 - \ell/n)\,z(\Gamma)$, $\ell = \lceil n/C \rceil$
-- statement:
--   For a unit-demand VRP instance with metric distances, $n \ge 1$ customers, capacity $C \ge 1$,
--   $\ell = \lceil n/C \rceil$, and any tour $\Gamma$ through the depot and all customers, there is a
--   feasible VRP solution of total length at most
--
--   $$ 2\ell\,\bar c + \Big(1 - \frac{\ell}{n}\Big) z(\Gamma). $$
--
--   This is the iterated optimal tour partition heuristic: cut the customer sequence of $\Gamma$
--   into $\ell$ consecutive blocks of at most $C$ customers starting at each of the $n$ customers in
--   turn, connect each block to the depot, and keep the best of the $n$ solutions. Over the $n$
--   solutions each customer is first and last on exactly $\ell$ routes and each tour edge is
--   omitted exactly $\ell$ times, so the average solution costs $2\ell\bar c + (1 - \ell/n)z(\Gamma)$
--   and the best is no worse. Applied to the optimal tour it gives the upper bound of Theorem 11.6.
-- source:
--   Lawrence V. Snyder and Zuo-Jun Max Shen, Fundamentals of Supply Chain Theory, 2nd ed., Wiley 2019, DOI 10.1002/9781119584445, pp. 495-496, Sect. 11.4.1, the proof of Theorem 11.6, the optimal tour partition and iterated optimal tour partition heuristics, Eq. (11.58)-(11.59)

import Definitions.Def_SupplyChainTheory_vrp

namespace SupplyChainTheory

theorem iotp_bound {n : ℕ} (c : Fin (n + 1) → Fin (n + 1) → ℝ) (hc : VRPMetric c)
    (hn : 1 ≤ n) (C : ℕ) (hC : 1 ≤ C) (L : List (Fin (n + 1))) (hL : IsCustomerTour L) :
    ∃ R, IsVRPSolution C R ∧ solutionCost c R
      ≤ 2 * ⌈(n : ℝ) / C⌉₊ * avgDepotDist c + (1 - (⌈(n : ℝ) / C⌉₊ : ℝ) / n) * routeCost c L := by sorry

end SupplyChainTheory
