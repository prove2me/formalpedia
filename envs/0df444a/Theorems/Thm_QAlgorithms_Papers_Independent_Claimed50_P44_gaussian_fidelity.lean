-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Claimed50_P44_gaussian_fidelity
-- name    : QAlgorithms.Papers.Independent.Claimed50.P44.gaussian_fidelity
-- status  : Open
-- author  : @Goku
-- created : 2026-10-20T11:06:51.312531+00:00
-- url     : https://prove2.me/theorems/cee25858-6546-4eae-85d7-a7c6c38c4a5d
-- title:
--   Outcome-averaged pure Gaussian teleportation fidelity
-- statement:
--   Let a normalized centered two-mode Gaussian resource have covariance $V=\begin{pmatrix}A&C\\ C^T&B\end{pmatrix}$ in the order $(x_A,p_A,x_B,p_B)$, satisfying the quantum uncertainty condition with $\hbar=1$ and vacuum covariance $I$. Let an independent pure one-mode Gaussian input have physical covariance $D$, $\det D=1$, and arbitrary mean $m$. Alice measures $X_+=(x_{\rm in}+x_A)/\sqrt2$ and $P_-=(p_{\rm in}-p_A)/\sqrt2$; Bob adds $\sqrt2(X_+,P_-)$ to his quadratures. Average over all measurement outcomes before taking the pure-input overlap. For $R=\operatorname{diag}(1,-1)$, define
--
--   $$E=2D+RAR^T+RC+C^TR^T+B.$$
--
--   Then $E$ is positive definite, $\det E>0$, the averaged output is normalized and is the convolution of the input Wigner function with the resource's teleportation kernel, and
--
--   $$F=\frac{2}{\sqrt{\det E}}.$$
--
--   The fidelity is independent of $m$; the overlap integrand is integrable. This connects the specified Bell instrument and feedforward to a covariance formula.
-- source:
--   Improving fidelity of continuous-variable teleportation via local operations, arXiv:quant-ph/0202102v3, PDF p. 2, §II, Eqs.(1)–(12)

import Definitions.Def_QAlgorithms_Papers_Independent_Claimed50_P44

noncomputable section

open MeasureTheory

open scoped Matrix ComplexOrder

namespace QAlgorithms.Papers.Independent.Claimed50.P44

open QAlgorithms.Papers.Independent.Dependency50.P10 (complexify physicalCovariance pureCovariance)

open QAlgorithms.Papers.Independent.Information100.P37 (quadratic)

/-- PDF p.2, Eqs.(1)-(12). The Bell measurement, conditional feedforward and
outcome average precede the overlap. Physicality supplies positive determinant;
the input displacement is arbitrary. Output convolution and normalization are
included to rule out zero-by-nonintegrability interpretations. -/
theorem gaussian_fidelity (A B C D : QuadratureMatrix)
    (hresource : PhysicalResource (resourceCov A B C)) (hinput : pureCovariance D modeSymplecticForm) :
    let W := resourceWigner (resourceCov A B C) 0
    let E := noiseBase D A B C 1
    E.PosDef ∧ 0 < E.det ∧
    ∀ mean : PhasePoint,
      (∀ z : PhasePoint, bellOutput (gaussianWigner D mean) W z =
        phaseIntegral (fun w => teleportKernel W (z - w) * gaussianWigner D mean w)) ∧
      phaseIntegral (bellOutput (gaussianWigner D mean) W) = 1 ∧
      phaseIntegral (bellOutcomeDensity (gaussianWigner D mean) W) = 1 ∧
      Integrable (fun x : ℝ × ℝ => gaussianWigner D mean ![x.1, x.2] *
        bellOutput (gaussianWigner D mean) W ![x.1, x.2]) ∧
      bellAverageFidelity D mean W = 2 / Real.sqrt E.det := by sorry

end QAlgorithms.Papers.Independent.Claimed50.P44

end
