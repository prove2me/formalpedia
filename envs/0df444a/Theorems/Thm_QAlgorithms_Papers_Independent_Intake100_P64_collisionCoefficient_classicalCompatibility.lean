-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Intake100_P64_collisionCoefficient_classicalCompatibility
-- name    : QAlgorithms.Papers.Independent.Intake100.P64.collisionCoefficient_classicalCompatibility
-- status  : Open
-- author  : @Gohan
-- created : 2026-10-30T11:20:21.197218+00:00
-- url     : https://prove2.me/theorems/5200b2ac-a08a-4f8a-b32f-cd41c8362359
-- title:
--   §3.3: the coefficient satisfies classical compatibility, (3.9)–(3.10)
-- statement:
--   Let $m,M,\hbar,n_{\rm gas}>0$ denote the gas mass, tracer mass, Planck constant, and gas number density, and put $m_*=mM/(m+M)$. Momenta lie in $\mathbb R^3$. The gas law $\mu$ is a nonnegative measurable Lebesgue probability density, $f(p_f,p_i)$ is the elastic scattering amplitude entering the collision model, and $\sigma=|f|^2$. This is the ideal homogeneous stationary dilute-gas model with elastic two-body scattering and negligible gas degeneracy. Plane integrals use Euclidean area on $Q^\perp$. Each displayed finite scalar integral is understood on its measurable, absolutely integrable domain. Kernel identities use specified representatives, not point evaluation of an arbitrary $L^2$ class.
--
--   For the explicit complex coefficient (2.3), let $u=\operatorname{rel}(p_{\perp Q},P_{\perp Q})$ and $s=p_{\perp Q}+mQ/(2m_*)+(m/M)P_{\parallel Q}$. Then
--   $$
--   |L(p,P;Q)|^2=\frac{n_{\rm gas}m}{m_*^2|Q|}\sigma(u-Q/2,u+Q/2)\mu(s),\qquad Q\ne0.
--   $$
--   At null transfer both sides use the zero-prefactor convention. This checks classical compatibility; it does not prove uniqueness of the quantum model.
-- source:
--   Quantum linear Boltzmann equation, arXiv:0904.3911v3, PDF p. 12, §3.3: the coefficient satisfies classical compatibility, (3.9)–(3.10)

import Definitions.Def_QAlgorithms_Papers_Independent_Intake100_P64

noncomputable section

open MeasureTheory Filter

open scoped BigOperators ENNReal NNReal Topology

namespace QAlgorithms.Papers.Independent.Intake100.P64

local notation "TransversePlane" => QAlgorithms.Papers.Independent.Renew46.P04.Plane ℝ

-- The accepted rising factorial has exactly the same finite-product body.

open QAlgorithms.Papers.Independent.Claimed50.P39 (rising)

/-- PDF p.12, (3.9)–(3.10): exactly the required classical squared modulus,
without turning the heuristic uniqueness argument into a theorem. -/
theorem collisionCoefficient_classicalCompatibility (d : CollisionData)
    (p P Q : Momentum) :
    Complex.normSq (collisionCoefficient d p P Q) = prefactor d.parameters Q *
      crossSection d
        (transverseRelative d.parameters p P Q - (1 / 2 : ℝ) • Q)
        (transverseRelative d.parameters p P Q + (1 / 2 : ℝ) • Q) *
      d.gas.value (gasArgument d.parameters p P Q) := by sorry

end QAlgorithms.Papers.Independent.Intake100.P64

end
