-- Prove2me | Theorems.Thm_SupplyChainTheory_rflp_ordered_assignments
-- name    : SupplyChainTheory.rflp_ordered_assignments
-- status  : Proved
-- author  : @naimengye
-- created : 2026-09-24T00:49:24.58871+00:00
-- url     : https://prove2.me/theorems/fb1e6f87-3bae-4b59-8145-e2f864f1a6e3
-- title:
--   Theorem 9.10: in any optimal RFLP solution, consecutive backup assignments are in order of cost, $c_{ij} \le c_{ik}$
-- statement:
--   **Theorem 9.10.** In any optimal solution to (RFLP) with positive demands and disruption
--   probability $0 < q < 1$, if customer $i$ is assigned to facility $j$ at level $r$ and to facility
--   $k$ at level $r + 1$, with $0 \le r < |J| - 2$, then $c_{ij} \le c_{ik}$.
--
--   The formulation imposes no constraint that a customer's level-$r$ facility be closer than its
--   level-$(r+1)$ facility; the theorem says that ordering by cost is always optimal, so it need
--   not be enforced. The book omits the proof (Problem 9.22): swapping the two assignments changes
--   the cost by $h_i q^r (1-q)^2 (c_{ik} - c_{ij})$ when neither is the emergency facility, and when
--   $k = u$ moving $u$ up to level $r$ and dropping $j$ changes it by $h_i q^r(1-q)(\theta_i - c_{ij})$;
--   optimality forces both to be nonnegative. The case $j = u$ cannot occur, since an assignment to
--   $u$ at level $r$ leaves nothing to assign at level $r + 1$ by (9.62).
-- source:
--   Lawrence V. Snyder and Zuo-Jun Max Shen, Fundamentals of Supply Chain Theory, 2nd ed., Wiley 2019, DOI 10.1002/9781119584445, p. 392, Sect. 9.6.3, Theorem 9.10: 'Proof. Omitted; see Problem 9.22'; the formulation is (9.61)-(9.67), pp. 391; after Snyder and Daskin (2005)

import Definitions.Def_SupplyChainTheory_disruptions

namespace SupplyChainTheory

theorem rflp_ordered_assignments {n m : ℕ} (h : Fin n → ℝ) (c : Fin n → Fin m → ℝ) (f : Fin m → ℝ)
    (q : ℝ) (u : Fin m) (hq0 : 0 < q) (hq1 : q < 1) (hh : ∀ i, 0 < h i)
    (x : Fin m → ℝ) (y : Fin n → Fin m → Fin m → ℝ) (hopt : RFLPOptimal h c f q u x y)
    (i : Fin n) (j k : Fin m) (r r' : Fin m) (hr : r.val + 2 < m) (hr' : r'.val = r.val + 1)
    (hj : y i j r = 1) (hk : y i k r' = 1) : c i j ≤ c i k := by sorry

end SupplyChainTheory
