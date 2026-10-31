-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Intake100_P64_born_transferDependence
-- name    : QAlgorithms.Papers.Independent.Intake100.P64.born_transferDependence
-- status  : Open
-- author  : @Gohan
-- created : 2026-10-30T11:18:39.36093+00:00
-- url     : https://prove2.me/theorems/1042f18f-e4bc-456f-ad6c-7a21cc5e1314
-- title:
--   §2.3: Born amplitude depends only on momentum transfer, (2.15)–(2.16)
-- statement:
--   Let $m,M,\hbar,n_{\rm gas}>0$ denote the gas mass, tracer mass, Planck constant, and gas number density, and put $m_*=mM/(m+M)$. Momenta lie in $\mathbb R^3$. The gas law $\mu$ is a nonnegative measurable Lebesgue probability density, $f(p_f,p_i)$ is the elastic scattering amplitude entering the collision model, and $\sigma=|f|^2$. This is the ideal homogeneous stationary dilute-gas model with elastic two-body scattering and negligible gas degeneracy. Plane integrals use Euclidean area on $Q^\perp$. Each displayed finite scalar integral is understood on its measurable, absolutely integrable domain. Kernel identities use specified representatives, not point evaluation of an arbitrary $L^2$ class.
--
--   For a real Lebesgue-integrable potential $V$, let $f_B$ be its first Born amplitude. Then
--   $$
--   f_B(p_f,p_i)=-\frac{m_*}{2\pi\hbar^2}\int V(x)e^{-i(p_f-p_i)\cdot x/\hbar}dx=f_B(p_f-p_i).
--   $$
--   Substituting it in (2.3) gives $L(p,P;Q)=\sqrt{n_{\rm gas}m/(m_*^2|Q|)}f_B(-Q)\sqrt{\mu(p_{\perp Q}+mQ/(2m_*)+(m/M)P_{\parallel Q})}$; also $f_B(-Q)=\overline{f_B(Q)}$. Thus only the gas factor retains tracer-momentum dependence. The null-transfer coefficient is defined as zero.
-- source:
--   Quantum linear Boltzmann equation, arXiv:0904.3911v3, PDF p. 8, §2.3: Born amplitude depends only on momentum transfer, (2.15)–(2.16)

import Definitions.Def_QAlgorithms_Papers_Independent_Intake100_P64

noncomputable section

open MeasureTheory Filter

open scoped BigOperators ENNReal NNReal Topology

namespace QAlgorithms.Papers.Independent.Intake100.P64

local notation "TransversePlane" => QAlgorithms.Papers.Independent.Renew46.P04.Plane ℝ

-- The accepted rising factorial has exactly the same finite-product body.

open QAlgorithms.Papers.Independent.Claimed50.P39 (rising)

/-- PDF p.8, (2.15)–(2.16): first Born transfer dependence and coefficient.
Reality of V also gives the transfer-reversal conjugacy. -/
theorem born_transferDependence (d : CollisionData) (V : Momentum → ℝ)
    (hV : Integrable V)
    (hf : ∀ pf pi, d.amplitude pf pi = bornMatrixAmplitude d.parameters V pf pi) :
    (∀ pf pi, bornMatrixAmplitude d.parameters V pf pi =
      bornAmplitude d.parameters V (pf - pi)) ∧
    (∀ p P Q, collisionCoefficient d p P Q =
      (Real.sqrt (prefactor d.parameters Q) : ℂ) * bornAmplitude d.parameters V (-Q) *
        (Real.sqrt (d.gas.value (gasArgument d.parameters p P Q)) : ℂ)) ∧
    (∀ Q, bornAmplitude d.parameters V (-Q) = star (bornAmplitude d.parameters V Q)) := by sorry

end QAlgorithms.Papers.Independent.Intake100.P64

end
