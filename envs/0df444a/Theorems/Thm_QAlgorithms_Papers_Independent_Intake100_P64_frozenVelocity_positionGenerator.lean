-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Intake100_P64_frozenVelocity_positionGenerator
-- name    : QAlgorithms.Papers.Independent.Intake100.P64.frozenVelocity_positionGenerator
-- status  : Open
-- author  : @Gohan
-- created : 2026-10-30T11:28:52.131954+00:00
-- url     : https://prove2.me/theorems/3536acb5-f3cb-4303-b120-dcf032195ee5
-- title:
--   §7.2.2: position generator for the frozen-velocity model, corrected normalization in (7.19)
-- statement:
--   Let $m,M,\hbar,n_{\rm gas}>0$ denote the gas mass, tracer mass, Planck constant, and gas number density, and put $m_*=mM/(m+M)$. Momenta lie in $\mathbb R^3$. The gas law $\mu$ is a nonnegative measurable Lebesgue probability density, $f(p_f,p_i)$ is the elastic scattering amplitude entering the collision model, and $\sigma=|f|^2$. This is the ideal homogeneous stationary dilute-gas model with elastic two-body scattering and negligible gas degeneracy. Plane integrals use Euclidean area on $Q^\perp$. Each displayed finite scalar integral is understood on its measurable, absolutely integrable domain. Kernel identities use specified representatives, not point evaluation of an arbitrary $L^2$ class.
--
--   Fix $P_0$, with finite positive $\Gamma(P_0)=M_{\rm out}(P_0)$. Let $J(P_0,Q)=M_{\rm in}^{\rm cl}(P_0+Q;Q)$ and $\mathcal P_{P_0}(Q)=J(P_0,Q)/\Gamma(P_0)$. Then $\int\mathcal P_{P_0}=1$ and its characteristic function $\Phi_{P_0}(S)=\int\mathcal P_{P_0}(Q)e^{iQ\cdot S/\hbar}dQ$ satisfies $\Phi_{P_0}(0)=1$. For the specified frozen-label model,
--   $$
--   (\mathcal L_{P_0}r)(X,X')=-\Gamma(P_0)[1-\Phi_{P_0}(X-X')]r(X,X').
--   $$
--   **Source correction:** the unnumbered formula below (7.19) omits $1/\Gamma(P_0)$; the normalization here is (7.9), required by (7.10) and by preservation of the position diagonal. Independent moderation remains pending. No approximation theorem for the full QLBE is asserted.
-- source:
--   Quantum linear Boltzmann equation, arXiv:0904.3911v3, PDF p. 37, §7.2.2: position generator for the frozen-velocity model, corrected normalization in (7.19)

import Definitions.Def_QAlgorithms_Papers_Independent_Intake100_P64

noncomputable section

open MeasureTheory Filter

open scoped BigOperators ENNReal NNReal Topology

namespace QAlgorithms.Papers.Independent.Intake100.P64

local notation "TransversePlane" => QAlgorithms.Papers.Independent.Renew46.P04.Plane ℝ

-- The accepted rising factorial has exactly the same finite-product body.

open QAlgorithms.Papers.Independent.Claimed50.P39 (rising)

open QAlgorithms.Papers.Independent.Dependency50.P13
  (TraceClass State relativeEntropy traceNormTopology)

open QAlgorithms.Papers.Independent.Next46.P09 (IsTraceLinear IsTraceCP)

/-- PDF pp.35,37, (7.9)–(7.10),(7.19), SOURCE CORRECTION:
printed: the unnumbered Phi formula below (7.19) omits 1/Gamma(P0).
changed: use the explicitly normalized probability law (7.9).
why: (7.10) and preservation of the diagonal require Phi(0)=1.
Independent moderation of this correction is still required. -/
theorem frozenVelocity_positionGenerator (d : CollisionData) (F : TransverseFrames)
    (P0 : Momentum) (hGamma : 0 < collisionLossRate d F P0)
    (hplane : ∀ᵐ Q : Momentum, Integrable (rateIntegrand d F P0 Q))
    (hloss : Integrable (outgoingIntensity d F P0)) (r : MomentumKernel) :
    (∫ Q, transferRate d F P0 Q / collisionLossRate d F P0) = 1 ∧
    frozenCharacteristic d F P0 0 = 1 ∧
    (∀ X Xprime, frozenPositionGenerator d F P0 r X Xprime =
      -(collisionLossRate d F P0 : ℂ) * (1 - frozenCharacteristic d F P0 (X - Xprime)) * r X Xprime) := by sorry

end QAlgorithms.Papers.Independent.Intake100.P64

end
