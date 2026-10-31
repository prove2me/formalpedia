-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Intake100_P34_entropy_cumulants
-- name    : QAlgorithms.Papers.Independent.Intake100.P34.entropy_cumulants
-- status  : Open
-- author  : @Gohan
-- created : 2026-10-30T18:07:36.899989+00:00
-- url     : https://prove2.me/theorems/370ecdaa-839a-4655-91c2-2c52f76043a9
-- title:
--   Theorem 3.4 — first and second cumulants of entropy transport
-- statement:
--   Assume detailed balance and positivity improvement on $B(\mathbb C^d)$, $d>0$, and let $\rho_+$ be the resulting faithful stationary density. Put $S_j=-\log\rho_j$, $I_j=L_j(S_j)$, $J_j=I_j-\rho_+(I_j)1$, and $J_j^+=L_j^*(S_j\rho_+)\rho_+^{-1}$. Write $D_j(A,B)=L_j(A^*B)-L_j(A^*)B-A^*L_j(B)$. Then
--
--   $$\partial_j e(0)=\rho_+(I_j)=-\bar s_j,\qquad\lim_{t\to\infty}\mathbb E_{\rho,t}s_j=\bar s_j,\qquad\sigma(\rho_+)=\sum_j\bar s_j.$$
--
--   Moreover,
--
--   $$\begin{aligned}\partial_k\partial_j e(0)={}&-\int_0^\infty\rho_+(e^{tL}(J_j)J_k^++e^{tL}(J_k)J_j^+)\,dt\\&+\int_0^\infty\rho_+(L_k(e^{tL}(J_j)S_k)+L_j(e^{tL}(J_k)S_j))\,dt\\&+\delta_{jk}\rho_+(D_j(S_j,S_j)).\end{aligned}$$
--
--   Both complex correlation integrals are absolutely convergent. All finite-time first and second moments exist, and the same Hessian is $\lim_{t\to\infty}t\operatorname{Cov}_{\rho,t}(s_j,s_k)$ for every initial state. These identities connect spectral derivatives with transport observables and fluctuations.
-- source:
--   Entropic fluctuations of quantum dynamical semigroups, arXiv:1305.4409v2, PDF p. 10, Theorem 3.4

import Definitions.Def_QAlgorithms_Papers_Independent_Intake100_P34

noncomputable section

open scoped BigOperators Matrix ComplexConjugate ENNReal NNReal Matrix.Norms.L2Operator ComplexOrder

open MeasureTheory Filter

attribute [local instance] Classical.propDecidable Classical.decEq

namespace QAlgorithms.Papers.Independent.Intake100.P34

open QAlgorithms (IsDensityMatrix)

open QAlgorithms.Papers.Independent.Dependency50.P16 (sandwich)

open QAlgorithms.Papers.Independent.Information100.P26 (Mat commutant scalars)

open QAlgorithms.Papers.Independent.Information100.P30 (MatrixMap IsPositiveMap)

open QAlgorithms.Papers.Independent.Information100.P56 (entropy)

open QAlgorithms.Papers.Independent.Information100.P69 (Faithful)

open QAlgorithms.Papers.Independent.Bridge50.P37 (hsAdjoint)

open QAlgorithms.Papers.Independent.Claimed50.P15
  (evaluate finiteRelativeEntropyNats entropyObservable)

open QAlgorithms.Papers.Independent.Claimed50.P43 (chaotic)

/-- PDF p.3: complex linear superoperators. -/
local notation "GeneratorMap" => fun d : ℕ => MatrixMap (Fin d) (Fin d)

/-- PDF pp.10,27–28, Theorem 3.4: both integral terms and the local dissipation term are
retained. J_j^+ is computed using the faithful stationary-density inverse. -/
theorem entropy_cumulants {d M : ℕ} (D : DBData d M) (hER : ER D) :
    (∀ j, countingCoordinateDerivative (entropySpectralCGF D) j 0 = evaluate (steadyDensity (reservoirGenerator D)) (entropyFlux D j) ∧
      evaluate (steadyDensity (reservoirGenerator D)) (entropyFlux D j) = -entropyMean D j) ∧
    (∀ rho, IsDensityMatrix rho → ∀ j,
      Tendsto (fun t : ℝ => lawMean (efcs D rho t) j) atTop (nhds (entropyMean D j))) ∧
    reservoirEntropyProduction D (steadyDensity (reservoirGenerator D)) = ((∑ j, entropyMean D j : ℝ) : EReal) ∧
    (∀ j k, IntegrableOn (currentCorrelation D j k) (Set.Ioi 0) ∧
      IntegrableOn (currentCorrection D j k) (Set.Ioi 0) ∧
      (coordinateHessianAtZero (entropySpectralCGF D) j k : ℂ) =
        -(∫ t in Set.Ioi (0 : ℝ), currentCorrelation D j k t) +
        (∫ t in Set.Ioi (0 : ℝ), currentCorrection D j k t) +
        (if j = k then expect (steadyDensity (reservoirGenerator D))
          (dissipation (D.generator j) (entropyObservable (D.rho j)) (entropyObservable (D.rho j))) else 0)) ∧
    (∀ rho, IsDensityMatrix rho → ∀ t : ℝ, 0 < t → ∀ j k,
      Integrable (fun s : EntropyCoordinates M => s j * s k) (efcs D rho t) ∧
      Integrable (fun s : EntropyCoordinates M => s j) (efcs D rho t)) ∧
    (∀ rho, IsDensityMatrix rho → ∀ j k,
      Tendsto (fun t : ℝ => t * ∫ s : EntropyCoordinates M,
        (s j - lawMean (efcs D rho t) j) * (s k - lawMean (efcs D rho t) k) ∂(efcs D rho t))
        atTop (nhds (coordinateHessianAtZero (entropySpectralCGF D) j k))) := by sorry

end QAlgorithms.Papers.Independent.Intake100.P34

end
