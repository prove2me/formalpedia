-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Claimed50_P35_multimodeGaussianNormBound
-- name    : QAlgorithms.Papers.Independent.Claimed50.P35.multimodeGaussianNormBound
-- status  : Open
-- author  : @Goku
-- created : 2026-10-20T10:36:29.237751+00:00
-- url     : https://prove2.me/theorems/57604c70-b406-4784-b58c-2a57861b7303
-- title:
--   IV.D: multimode Gaussian norm estimate
-- statement:
--   Let $T$ be a trace-class-preserving complex-linear finite-mode Bosonic transformation with Gaussian multiplier $f(z)=\exp(-z^TBz/2)$, where $B$ is real symmetric positive definite. Suppose its defect form $\Delta''$ is nondegenerate. In normal coordinates $z=S u$ satisfying $\Delta''(Su,Sv)=\Delta(u,v)$ and $B[Su]=\hbar\sum_j\gamma_j(u_{q_j}^2+u_{p_j}^2)$, with $\gamma_j>0$, one has
--
--   $$\|T\|_\diamond\le\prod_j\max\{1,(2\gamma_j)^{-1}\}.$$
--
--   The CCR representations are regular and irreducible with $\hbar>0$. The parameters belong to the defect form, not the original input form. This is the source's upper estimate, with no equality assertion.
-- source:
--   Evaluating Capacities of Bosonic Gaussian Channels, arXiv:quant-ph/9912067v1, PDF p. 9, IV.D: multimode Gaussian norm estimate

import Definitions.Def_QAlgorithms_Papers_Independent_Claimed50_P35

noncomputable section

open Filter MeasureTheory

open scoped Topology ENNReal NNReal BigOperators

attribute [local instance] Classical.propDecidable

attribute [local instance] Classical.decEq

attribute [local instance] IsStarNormal.instContinuousFunctionalCalculus

namespace QAlgorithms.Papers.Independent.Claimed50.P35

open QAlgorithms.RealRegisters (Hilbert)

open QAlgorithms.Papers.Independent.Dependency50.P33

open QAlgorithms.Papers.Independent.Dependency50.P39
  (displacementMatrix attenuatorMatrix amplifierMatrix thermalMatrix)

open QAlgorithms.Papers.Independent.Frontier30.P14
  (Operation conjugateKernel composeKernel partialRight isometryCoeff identityCoeff)

open QAlgorithms.Papers.Independent.Frontier30.P21 (bosonicEntropy)

open QAlgorithms.Papers.Independent.Frontier18.P18 (operatorCoeff boundedOperator)

/-- IV.D, p.9: multimode Gaussian upper bound, not a matching equality. -/
theorem multimodeGaussianNormBound {I J : Type} [Nonempty I] [Nonempty J]
    {s : ℕ} {hbar : ℝ} (W : ScaledWeylRepresentation I s hbar) (Wout : ScaledWeylRepresentation J s hbar)
    (T : Operation I J) (hT : TraceLinear T)
    (K B : Matrix (Fin s × Fin 2) (Fin s × Fin 2) ℝ)
    (hBsym : B.transpose = B) (hBpos : B.PosDef)
    (hlaw : LinearBosonic W Wout T K (gaussianFunction 0 B))
    (S : InterleavedPhase s ≃ₗ[ℝ] InterleavedPhase s) (gamma : Fin s → ℝ)
    (hmodes : NoiseNormalModes hbar K B S gamma) :
    stabilizedTraceClassNorm T ≤ ∏ j : Fin s, ENNReal.ofReal (max 1 (1 / (2 * gamma j))) := by sorry

end QAlgorithms.Papers.Independent.Claimed50.P35

end
