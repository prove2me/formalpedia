-- Prove2me | Theorems.Thm_ServiceParts_Allocation_netInv_normal
-- name    : ServiceParts.Allocation.netInv_normal
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-09-30T23:11:31.9942+00:00
-- url     : https://prove2.me/theorems/29070623-36a9-4dbf-8da7-10416bd7b22c
-- title:
--   Section 7.2.1.2 — warehouse net inventory is normal with explicit mean and variance
-- statement:
--   In the Eppen–Schrage system (see `PoolingSystem`): $m \ge 1$ warehouses, i.i.d. normal demands $d_{jt}$ with mean $\mu_j$ and variance $\sigma_j^2 > 0$ independent across warehouses and periods, lead times $D$ and $A$, and system inventory position $s$. Let the depot allocate the $s - Y_0$ units on hand by the balanced allocation $x_j$, and let $z_j = x_j - Y_j$ be the net inventory at warehouse $j$ at the end of a period. Then $z_j$ is normally distributed with mean
--   $$E[z_j] = \Bigl(s - (D + A + 1) \sum_{i=1}^m \mu_i\Bigr) \cdot \frac{\sigma_j}{\sum_{i=1}^m \sigma_i}$$
--   and variance
--   $$\operatorname{Var}[z_j] = (A+1)\sigma_j^2 + \Bigl(\frac{\sigma_j}{\sum_{i=1}^m \sigma_i}\Bigr)^2 \cdot D \cdot \sum_{i=1}^m \sigma_i^2.$$
--
--   These moments reduce the choice of the system stock level $s$ to a newsvendor problem in one standardized variable.
--
--   **Formalization Note** The law of $z_j$ is asserted as an equality of measures, `P.map z_j = gaussianReal mean variance`.
-- source:
--   Muckstadt, Analysis and Algorithms for Service Parts Supply Chains, Springer 2005, DOI 10.1007/b138879, pp. 156-157, Section 7.2.1.2

import Mathlib
import Definitions.Def_ServiceParts_Allocation_PoolingSystem

open MeasureTheory ProbabilityTheory

namespace ServiceParts.Allocation

/-- Muckstadt (2005), Section 7.2.1.2, pp. 156–157: under the balanced allocation, the
warehouse net inventory `z_j` is normal with mean `(s - (D + A + 1) Σ_i μ_i) σ_j / Σ_i σ_i`
and variance `(A + 1) σ_j² + (σ_j / Σ_i σ_i)² D Σ_i σ_i²`. -/
theorem netInv_normal {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
    {m : ℕ} (S : PoolingSystem Ω P m) (s : ℝ) (j : Fin m) :
    P.map (S.netInv s j) =
      gaussianReal ((s - (S.D + S.A + 1) * ∑ i, S.μ i) * (S.σ j / ∑ i, S.σ i))
        (Real.toNNReal ((S.A + 1) * S.σ j ^ 2 +
          (S.σ j / ∑ i, S.σ i) ^ 2 * S.D * ∑ i, S.σ i ^ 2)) := by sorry

end ServiceParts.Allocation
