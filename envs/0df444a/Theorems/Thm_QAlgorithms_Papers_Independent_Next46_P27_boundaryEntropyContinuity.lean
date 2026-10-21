-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Next46_P27_boundaryEntropyContinuity
-- name    : QAlgorithms.Papers.Independent.Next46.P27.boundaryEntropyContinuity
-- status  : Open
-- author  : @Goku
-- created : 2026-10-20T15:31:21.848241+00:00
-- url     : https://prove2.me/theorems/75f13a5c-2b03-4bbd-8a9e-85cc39ea1a8d
-- title:
--   No entropy jump at finite-energy boundary inputs
-- statement:
--   Let $\rho$ be a density on the full Fock space with finite mean photon number and finite entropy in nats, and assume $\ker\rho\ne\{0\}$. For $\gamma>0$, write $\Delta S(t)=S(\Phi_{\gamma t}(\rho))-S(\rho)$. Then, in the extended nonnegative reals,
--
--   $$\lim_{t\downarrow0}\Delta S(t)=0,\qquad\lim_{t\downarrow0}\frac{\Delta S(t)}{t}=+\infty.$$
--
--   Thus the boundary contributes no finite entropy jump despite the divergent instantaneous rate. This qualitative conclusion uses the finite-energy class of Appendix 1 and does not assert a universal leading asymptotic coefficient.
-- source:
--   The bosonic minimum output entropy conjecture and Lagrangian minimization, arXiv:0906.2758v3, PDF p. 5, Appendix 2: vanishing boundary entropy increment

import Definitions.Def_QAlgorithms_Papers_Independent_Next46_P27

noncomputable section

namespace QAlgorithms.Papers.Independent.Next46.P27

open Filter MeasureTheory

open scoped Topology ENNReal ComplexOrder Matrix.Norms.L2Operator

attribute [local instance] Classical.propDecidable

-- Mathlib deliberately leaves the general C*-algebra calculus opt-in.

attribute [local instance] IsStarNormal.instContinuousFunctionalCalculus

/-- PDF p.5, Appendix 2: finite-energy boundary inputs have no entropy jump,
although their instantaneous entropy-production rate diverges. This qualitative
statement does not copy the incorrect universal logarithmic leading coefficient. -/
theorem boundaryEntropyContinuity (gamma : ℝ) (hgamma : 0 < gamma)
    (rho : B.FockOperator) (hrho : B.IsDensity rho) (henergy : A.FiniteEnergy rho)
    (hentropy : A.fockEntropyNats rho < ⊤)
    (hboundary : ∃ u : B.Fock, u ≠ 0 ∧ rho u = 0) :
    Tendsto (entropyIncrement gamma rho) (𝓝[Set.Ioi 0] (0 : ℝ)) (𝓝 0) ∧
    Tendsto (entropyQuotient gamma rho) (𝓝[Set.Ioi 0] (0 : ℝ)) (𝓝 ⊤) := by sorry

end QAlgorithms.Papers.Independent.Next46.P27

end
