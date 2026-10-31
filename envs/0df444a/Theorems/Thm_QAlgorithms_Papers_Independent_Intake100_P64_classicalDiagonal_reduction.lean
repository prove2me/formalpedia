-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Intake100_P64_classicalDiagonal_reduction
-- name    : QAlgorithms.Papers.Independent.Intake100.P64.classicalDiagonal_reduction
-- status  : Open
-- author  : @Gohan
-- created : 2026-10-30T11:17:00.053514+00:00
-- url     : https://prove2.me/theorems/9aa0f6d9-6805-4b45-841b-2c3d6237f7fa
-- title:
--   §2.2: classical diagonal reduction, (2.9), (2.13)–(2.14)
-- statement:
--   Let $m,M,\hbar,n_{\rm gas}>0$ denote the gas mass, tracer mass, Planck constant, and gas number density, and put $m_*=mM/(m+M)$. Momenta lie in $\mathbb R^3$. The gas law $\mu$ is a nonnegative measurable Lebesgue probability density, $f(p_f,p_i)$ is the elastic scattering amplitude entering the collision model, and $\sigma=|f|^2$. This is the ideal homogeneous stationary dilute-gas model with elastic two-body scattering and negligible gas degeneracy. Plane integrals use Euclidean area on $Q^\perp$. Each displayed finite scalar integral is understood on its measurable, absolutely integrable domain. Kernel identities use specified representatives, not point evaluation of an arbitrary $L^2$ class.
--
--   Let $g(P)=r(P,P)$ be the diagonal profile and $J(P,Q)=\frac{n_{\rm gas}m}{m_*^2|Q|}\int_{Q^\perp}\mu(k+\frac{m}{2m_*}Q+\frac mM P_{\parallel Q})\sigma(\operatorname{rel}(k,P_{\perp Q})-Q/2,\operatorname{rel}(k,P_{\perp Q})+Q/2)dk$, where $\operatorname{rel}(p,P)=m_*p/m-m_*P/M$. Then
--   $$
--   M_{\rm in}(P,P;Q)=J(P-Q,Q),\qquad (\mathcal Lr)(P,P)=\int J(P-Q,Q)g(P-Q)dQ-M_{\rm out}(P)g(P).
--   $$
--   This is exactly the classical linear Boltzmann collision expression. In its gain term the gas shift contains $\frac mM(P_{\parallel Q}-Q)$.
-- source:
--   Quantum linear Boltzmann equation, arXiv:0904.3911v3, PDF p. 7, §2.2: classical diagonal reduction, (2.9), (2.13)–(2.14)

import Definitions.Def_QAlgorithms_Papers_Independent_Intake100_P64

noncomputable section

open MeasureTheory Filter

open scoped BigOperators ENNReal NNReal Topology

namespace QAlgorithms.Papers.Independent.Intake100.P64

local notation "TransversePlane" => QAlgorithms.Papers.Independent.Renew46.P04.Plane ℝ

-- The accepted rising factorial has exactly the same finite-product body.

open QAlgorithms.Papers.Independent.Claimed50.P39 (rising)

/-- PDF pp.7,10–11, (2.9),(2.13)–(2.14): diagonal reduction to the classical
collision equation, retaining the correct shifted gas argument. -/
theorem classicalDiagonal_reduction (d : CollisionData) (F : TransverseFrames)
    (r : MomentumKernel) (nu : Momentum → ℝ) (P : Momentum)
    (hdiag : ∀ p, r p p = (nu p : ℂ)) (hdom : KernelDomain d F r P P)
    (hgain : Integrable (fun Q => transferRate d F (P - Q) Q * nu (P - Q))) :
    (∀ Q, Integrable (rateIntegrand d F (P - Q) Q) →
      quantumGain d F P P Q = (transferRate d F (P - Q) Q : ℂ)) ∧
    collisionKernel d F r P P = (classicalGenerator d F nu P : ℂ) := by sorry

end QAlgorithms.Papers.Independent.Intake100.P64

end
