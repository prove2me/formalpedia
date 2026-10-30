-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Advance50_P22_parametric_entropy_derivatives
-- name    : QAlgorithms.Papers.Independent.Advance50.P22.parametric_entropy_derivatives
-- status  : Open
-- author  : @Gohan
-- created : 2026-10-29T12:09:51.676988+00:00
-- url     : https://prove2.me/theorems/73e738e5-3004-465e-9370-93e1482f8547
-- title:
--   Section III B, Eqs.(22)–(23): derivatives along the constructed clocks
-- statement:
--   Let $n,K\ge1$, let $\Phi$ be a Gaussian scattering channel, and let its independent normalized inputs have finite mean photon number. Take clocks solving the entropy clock equations and fix $\tau>0$. Write $S_\alpha(\tau)$ and $S_Y(\tau)$ for the corresponding input and output entropies. On the finite twice-differentiable displacement-relative-entropy domain, the full Fisher Hessians satisfy
--
--   $$\frac{dS_\alpha}{d\tau}=\frac14e^{S_\alpha/n}\operatorname{tr}(J_\alpha\gamma_\alpha),\qquad \frac{dS_Y}{d\tau}=\frac14\left(\sum_\alpha\lambda_\alpha e^{S_\alpha/n}\right)\operatorname{tr}J_Y.$$
--
--   The input formula is evaluated only for nonsingular blocks. Singular inputs have zero entropy derivative without a Fisher evaluation. If all blocks are singular, the output entropy derivative is zero without an output Hessian assumption. These are derivative conclusions along the constructed clocks.
-- source:
--   The multi-mode quantum Entropy Power Inequality, arXiv:1408.6410v2, PDF p. 4, Section III B, Eqs.(22)–(23): derivatives along the constructed clocks

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

/-- PDF p.4, Section III B, (22)--(23): both derivatives along entropy clocks.
Frozen singular inputs have zero derivative without a Fisher evaluation. If every
weight vanishes the output derivative is zero, even for a nonregular output.
Otherwise the output Hessian is used only on its explicit finite twice-differentiability domain. -/
theorem parametric_entropy_derivatives {n K : ℕ} (hn : 0 < n) (hK : 0 < K)
    (C : Scattering n K) (rho : Fin K → State (FockIndex n))
    (hEnergy : ∀ a, FiniteMeanEnergy (rho a).coefficients)
    (clock : Fin K → ℝ → ℝ)
    (hclock : EntropyClocks C.block (fun a => (rho a).coefficients) clock)
    (tau : ℝ) (htau : 0 < tau) :
    (∀ a, (C.block a).det ≠ 0 →
      MatrixFisherRegular (anisotropicHeat (inputNoise (C.block a))
        (clock a tau) (rho a).coefficients) →
      HasDerivAt (fun u => evolvedInputEntropyNats C.block (fun b => (rho b).coefficients) a (clock a u))
        (Real.exp (evolvedInputEntropyNats C.block (fun b => (rho b).coefficients) a (clock a tau) /
          (n : ℝ)) * (matrixFisher (anisotropicHeat (inputNoise (C.block a))
            (clock a tau) (rho a).coefficients) * inputNoise (C.block a)).trace / 4) tau) ∧
    (∀ a, (C.block a).det = 0 →
      HasDerivAt (fun u => evolvedInputEntropyNats C.block (fun b => (rho b).coefficients) a (clock a u)) 0 tau) ∧
    (let Y := fun u => C.channel (independentInput (evolvedInputs C.block
        (fun a => (rho a).coefficients) (fun a => clock a u)))
     ((∀ a, (C.block a).det = 0) →
       HasDerivAt (fun u => (extendedEntropyNats (Y u)).toReal) 0 tau) ∧
     ((∃ a, (C.block a).det ≠ 0) → MatrixFisherRegular (Y tau) →
       HasDerivAt (fun u => (extendedEntropyNats (Y u)).toReal)
         ((∑ a, determinantWeight (C.block a) *
           Real.exp (evolvedInputEntropyNats C.block (fun b => (rho b).coefficients) a (clock a tau) /
             (n : ℝ))) * (matrixFisher (Y tau)).trace / 4) tau)) := by sorry

end QAlgorithms.Papers.Independent.Advance50.P22

end
