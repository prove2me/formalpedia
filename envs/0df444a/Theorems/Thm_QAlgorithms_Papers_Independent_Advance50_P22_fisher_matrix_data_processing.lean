-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Advance50_P22_fisher_matrix_data_processing
-- name    : QAlgorithms.Papers.Independent.Advance50.P22.fisher_matrix_data_processing
-- status  : Open
-- author  : @Gohan
-- created : 2026-10-29T12:10:48.905188+00:00
-- url     : https://prove2.me/theorems/01817883-c005-4d33-be90-8ce425bb5503
-- title:
--   Section III B, Eqs.(27)–(28): block Fisher matrix inequality
-- statement:
--   Let $n,K\ge1$, let $\Phi$ be a Gaussian scattering channel with real blocks $M_\alpha$, and let $\rho_\alpha$ be independent normalized full $n$-mode densities. Set $\rho_Y=\Phi(\bigotimes_\alpha\rho_\alpha)$ and $y=\sum_\alpha M_\alpha x_\alpha$. The extended relative entropies obey
--
--   $$D(\rho_Y\Vert D_y\rho_YD_y^\dagger)\le\sum_\alpha D(\rho_\alpha\Vert D_{x_\alpha}\rho_\alpha D_{x_\alpha}^\dagger).$$
--
--   If each input and the output displacement divergence is finite near zero and twice Frechet differentiable in the explicit derivative domain, their Hessians obey the block Loewner inequality
--
--   $$\bigl(M_\alpha^TJ_YM_\beta\bigr)_{\alpha\beta}\preceq\operatorname{diag}(J_1,\ldots,J_K).$$
--
--   Lean states the latter as the quadratic-form inequality for every collection of real phase vectors. All cross blocks are retained; the extended divergence clause has no moment hypothesis.
-- source:
--   The multi-mode quantum Entropy Power Inequality, arXiv:1408.6410v2, PDF p. 4, Section III B, Eqs.(27)–(28): block Fisher matrix inequality

import Definitions.Def_QAlgorithms_Papers_Independent_Advance50_P22

noncomputable section

open Filter MeasureTheory

open scoped BigOperators ENNReal Topology

namespace QAlgorithms.Papers.Independent.Advance50.P22

attribute [local instance] Classical.propDecidable Classical.decEq

open QAlgorithms.Papers.Independent.Dependency50.P33
  (State IsDensity IsTraceClassChannel)

open QAlgorithms.Papers.Independent.Frontier18.P07
  (extendedEntropyNats extendedRelativeEntropyNats)

open QAlgorithms.Papers.Independent.Claimed50.P19
  (FockIndex DensityKernel Cov PhysicalCovariance FiniteMeanEnergy
   productWeyl weylArgument multimodeWeylTrace)

open QAlgorithms.Papers.Independent.Frontier30.P08
  (QuadratureIndex interleavedSymplecticForm)

open QAlgorithms.Papers.Independent.Next46.P17
  (bosonicEntropyPower conjugateCoefficient firstMoments quadratureCovariance
   gaussianCoefficient gaussification)

open QAlgorithms.Papers.Independent.Information100.P49 (symplecticEntropy)

/-- PDF p.4, Section III B, (27)--(28): extended relative-entropy contraction
and the entire block matrix Hessian inequality, including every cross block.
The quadratic-form conclusion is exactly Loewner order on the real block matrix.
Only the Hessian clause requires the finite twice-differentiability domain. -/
theorem fisher_matrix_data_processing {n K : ℕ} (hn : 0 < n) (hK : 0 < K)
    (C : Scattering n K) (rho : Fin K → State (FockIndex n)) :
    (∀ x : Fin K → InterleavedCoordinateVector n,
      displacementDivergence (C.channel (independentInput (fun a => (rho a).coefficients)))
        (∑ a, (C.block a).mulVec (x a)) ≤
      ∑ a, displacementDivergence (rho a).coefficients (x a)) ∧
    ((∀ a, MatrixFisherRegular (rho a).coefficients) →
      MatrixFisherRegular (C.channel (independentInput (fun a => (rho a).coefficients))) →
      ∀ v : Fin K → InterleavedCoordinateVector n,
        (∑ a, ∑ b, ∑ i, ∑ j, v a i *
          ((C.block a).transpose *
            matrixFisher (C.channel (independentInput (fun c => (rho c).coefficients))) *
              C.block b) i j * v b j) ≤
        ∑ a, ∑ i, ∑ j, v a i * matrixFisher (rho a).coefficients i j * v a j) := by sorry

end QAlgorithms.Papers.Independent.Advance50.P22

end
