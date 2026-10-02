-- Prove2me | Theorems.Thm_ServiceParts_Allocation_critical_fractile
-- name    : ServiceParts.Allocation.critical_fractile
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-09-30T23:12:44.59835+00:00
-- url     : https://prove2.me/theorems/817d8382-99ec-4b75-ad1c-6ee3d7cde128
-- title:
--   Section 7.2.1.2 — the optimal system stock level solves Φ(z) = b/(b+h)
-- statement:
--   In the Eppen–Schrage system (see `PoolingSystem`) with holding cost $h > 0$ and backorder cost $b > 0$, let the depot use the balanced allocation and let $z_j$ be the net inventory at warehouse $j$ at the end of a period, a function of the system inventory position $s$. Set
--   $$z = \frac{s - (D+A+1)\sum_{i=1}^m \mu_i}{\bigl[(A+1)\bigl(\sum_{i=1}^m \sigma_i\bigr)^2 + D \sum_{i=1}^m \sigma_i^2\bigr]^{1/2}}.$$
--   Then $s$ minimizes the expected holding and backorder cost per period
--   $$\sum_{j=1}^m E\bigl[h\,(z_j)^+ + b\,(z_j)^-\bigr]$$
--   over all real $s'$ if and only if
--   $$\Phi(z) = \frac{b}{b+h}.$$
--
--   Since $z$ does not depend on the warehouse, one critical fractile determines the system stock level, which is the basis of the book's comparison of the depot system with a single warehouse and with $m$ independent warehouses.
--
--   **Formalization Note** The book writes that "the optimal value for $z$, and hence $s$, can be found by setting $\Phi(z) = b/(b+h)$"; the statement is the corresponding characterization of the minimizers of the total expected cost, in both directions. The expected cost uses $b\,E[(z_j)^-]$, correcting a sign slip in the first cost display on p. 157 (see `PoolingSystem`).
-- source:
--   Muckstadt, Analysis and Algorithms for Service Parts Supply Chains, Springer 2005, DOI 10.1007/b138879, pp. 157-158, Section 7.2.1.2

import Mathlib
import Definitions.Def_ServiceParts_Allocation_PoolingSystem

open MeasureTheory ProbabilityTheory

namespace ServiceParts.Allocation

/-- Muckstadt (2005), Section 7.2.1.2, pp. 157–158: a system inventory position `s`
minimizes the expected holding and backorder cost per period summed over the warehouses
if and only if `Φ(z) = b / (b + h)`, with
`z = (s - (D + A + 1) Σ_i μ_i) / [(A + 1)(Σ_i σ_i)² + D Σ_i σ_i²]^{1/2}`. -/
theorem critical_fractile {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    [IsProbabilityMeasure P] {m : ℕ} (S : PoolingSystem Ω P m) (s : ℝ) :
    (∀ s' : ℝ, S.expectedCost s ≤ S.expectedCost s') ↔
      stdNormalCdf (S.zScore s) = S.b / (S.b + S.h) := by sorry

end ServiceParts.Allocation
