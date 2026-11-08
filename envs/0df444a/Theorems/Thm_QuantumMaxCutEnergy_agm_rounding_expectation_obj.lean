-- Prove2me | Theorems.Thm_QuantumMaxCutEnergy_agm_rounding_expectation_obj
-- name    : QuantumMaxCutEnergy.agm_rounding_expectation_obj
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-07T15:16:57.997386+00:00
-- url     : https://prove2.me/theorems/9c3fb0e3-5668-410d-aa33-34288e367eaf
-- title:
--   Summing the rank-three rounding bound from pairs to the objective
-- statement:
--   **From pair means to the objective: the aggregation step of the rank-three rounding.**
--
--   Let $\mu$ be a probability measure on Bloch assignments $r=(r_1,\dots,r_n)$, $r_i\in\mathbb R^3$, such that for every pair of vertices
--   $$\mathbb E_\mu\Big[\sum_{a=1}^{3} r_{ia}r_{ja}\Big]\;\le\;0.046+0.954\,X_{ij},$$
--   and suppose all these pair correlations are integrable. Then
--   $$0.954\;\cdot\;\mathrm{obj}(X)\;\le\;\mathbb E_\mu\big[\mathrm{obj}(r)\big],$$
--   where $\mathrm{obj}(M)=\tfrac14\sum_{i,j}A(G)_{ij}(1-M_{ij})$ is the Max-Cut relaxation objective of the graph's weight matrix, and $\mathrm{obj}(r)$ is that same objective evaluated at the Gram matrix $M_{ij}=\sum_a r_{ia}r_{ja}$ of the Bloch assignment.
--
--   **Why the constant $0.046$ is right.** Subtracting the pair bound from $1$,
--   $$1-\mathbb E\Big[\sum_a r_{ia}r_{ja}\Big]\;\ge\;1-0.046-0.954\,X_{ij}\;=\;0.954\,(1-X_{ij})+\big(1-0.046-0.954\big),$$
--   and the residual constant vanishes *exactly* because $0.046+0.954=1$. So multiplying by $A_{ij}\ge0$ and summing leaves no error term:
--   $$\mathbb E[\mathrm{obj}(r)]=\tfrac14\sum_{i,j}A_{ij}\Big(1-\mathbb E\Big[\sum_a r_{ia}r_{ja}\Big]\Big)\;\ge\;\tfrac14\sum_{i,j}A_{ij}\cdot 0.954\,(1-X_{ij})\;=\;0.954\,\mathrm{obj}(X).$$
--
--   The inequality is stated on the double sum rather than on the edge sum, which is why neither symmetry of $X$ nor a reindexing by the edge set is needed: the per-pair bound holds for every ordered pair and the weights are nonnegative. The analytic content is linearity of the integral over the finite sums $\sum_{i,j}$, together with $\int 1\,\mathrm d\mu=1$ for a probability measure.
--
--   This is the step that turns the per-pair rounding identity into a statement about the quantity the approximation guarantee is measured by.
-- source:
--   Anshu-Gosset-Morenz rounding, TQC 2020, doi 10.4230/LIPIcs.TQC.2020.7: aggregation of the per-edge correlation bound into the Max-Cut relaxation objective; uses the platform theorem QuantumMaxCutEnergy.rank3_gaussian_rounding_distribution.

import Mathlib
import Definitions.Def_QuantumMaxCutEnergyEstimationModel
import Definitions.Def_QuantumMaxCutEnergy_weightMatrix
import Definitions.Def_ModernConvex_Relaxations_SignRelaxations

open MeasureTheory Matrix
open scoped BigOperators

namespace QuantumMaxCutEnergy

/-- **The rounding bound at the level of the objective.** -/
theorem agm_rounding_expectation_obj (G : Input) (X : Matrix (Fin G.n) (Fin G.n) ℝ)
    (μ : Measure (Fin G.n → Fin 3 → ℝ)) [IsProbabilityMeasure μ]
    (hint : ∀ i j : Fin G.n,
      Integrable (fun r : Fin G.n → Fin 3 → ℝ => ∑ a : Fin 3, r i a * r j a) μ)
    (hpair : ∀ i j, ∫ r, (∑ a : Fin 3, r i a * r j a) ∂μ ≤ 0.046 + 0.954 * X i j) :
    (0.954 : ℝ) * ModernConvex.Relaxations.maxcutRelaxationObjective (weightMatrix G) X
      ≤ ∫ r, ModernConvex.Relaxations.maxcutRelaxationObjective (weightMatrix G)
          (Matrix.of fun i j => ∑ a : Fin 3, r i a * r j a) ∂μ := by sorry

end QuantumMaxCutEnergy
