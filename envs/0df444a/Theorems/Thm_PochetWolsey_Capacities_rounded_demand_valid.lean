-- Prove2me | Theorems.Thm_PochetWolsey_Capacities_rounded_demand_valid
-- name    : PochetWolsey.Capacities.rounded_demand_valid
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-10-29T02:27:57.591947+00:00
-- url     : https://prove2.me/theorems/08a98213-2a55-48db-a2a5-4cfac40e8497
-- title:
--   Proposition 9.2 — rounded cumulative demand inequalities
-- statement:
--   Let $n\ge1$, $C>0$, and $0\le d_t\le C$ for $1\le t\le n$. Write $d_{1t}=\sum_{u=1}^t d_u$, and assume the discrete lot-sizing feasible set $X^{\mathrm{DLS-CC}}$ is nonempty.
--
--   Every binary feasible setup vector $y$ satisfies
--   $$
--   \sum_{u=1}^t y_u\ge\left\lceil\frac{d_{1t}}C\right\rceil\qquad(1\le t\le n).
--   $$
--   These inequalities express the integral number of capacity-sized production opportunities required by each prefix of the horizon.
--
--   **Formalization Note** Periods use zero-based `Fin n` coordinates; the prefix sum through a coordinate includes it. Integer ceilings are cast to real numbers for comparison.
-- source:
--   Pochet and Wolsey, Production Planning by Mixed Integer Programming, Springer 2006, DOI 10.1007/0-387-33477-7, p. 276 (PDF 289), Proposition 9.2

import Mathlib
import Definitions.Def_PochetWolsey_Capacities_Model

namespace PochetWolsey.Capacities

/-- Proposition 9.2. The set in hfeas is (9.1)-(9.2), written out for auditing. -/
theorem rounded_demand_valid {n : ℕ} (hn : 0 < n) (C : ℝ) (hC : 0 < C)
    (d : Fin n → ℝ) (hd : ∀ t, 0 ≤ d t ∧ d t ≤ C)
    (hfeas : ({y : Fin n → ℝ | (∀ u, y u = 0 ∨ y u = 1) ∧
      ∀ t, (∑ u ∈ Finset.Iic t, d u) ≤ C * ∑ u ∈ Finset.Iic t, y u} : Set _).Nonempty)
    (y : Fin n → ℝ) (hy : ∀ u, y u = 0 ∨ y u = 1)
    (hcover : ∀ t, (∑ u ∈ Finset.Iic t, d u) ≤ C * ∑ u ∈ Finset.Iic t, y u) :
    ∀ t, (⌈(∑ u ∈ Finset.Iic t, d u) / C⌉ : ℤ) ≤
      (∑ u ∈ Finset.Iic t, y u) := by sorry

end PochetWolsey.Capacities
