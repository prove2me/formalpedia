-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Extend50_P36_isotropic_two_joinability
-- name    : QAlgorithms.Papers.Independent.Extend50.P36.isotropic_two_joinability
-- status  : Open
-- author  : @Gohan
-- created : 2026-10-29T13:56:50.322609+00:00
-- url     : https://prove2.me/theorems/9a4cf3bb-2e13-49a6-be7e-d51ff1f63863
-- title:
--   Corollary III.4: two isotropic marginals
-- statement:
--   Let $d\ge2$ be an integer. Write $\rho_W(\psi)$ for the $d$-dimensional Werner state with swap expectation $\psi\in[-1,1]$, and $\rho_I(\phi)$ for the isotropic state with $\phi=dF\in[0,d]$, where $F$ is its overlap with the normalized maximally entangled vector. A joining state is a positive semidefinite operator of trace one having the specified ordered pair marginals.
--
--   For $a,b\in[0,d]$, the isotropic AB and AC states are joinable if and only if
--   $$(a,b)\in\operatorname{conv}\left(\{(x,y):(x+y-d)^2+(x-y)^2/(d^2-1)=1\}\cup\{(0,0)\}\right).$$
--   The convex hull includes the entire filled ellipse and the additional origin region.
-- source:
--   Compatible quantum correlations: on extension problems for Werner and isotropic states, arXiv:1305.1342v3, PDF p. 9, Corollary III.4: two isotropic marginals

import Definitions.Def_QAlgorithms_Papers_Independent_Extend50_P36

noncomputable section

open scoped Matrix ComplexConjugate Matrix.Norms.Elementwise

open MeasureTheory

namespace QAlgorithms.Papers.Independent.Extend50.P36

attribute [local instance] Classical.propDecidable Classical.decEq

-- Exact accepted matrix alias; tensor reductions below compose frozen superoperators.

open QAlgorithms.Papers.Independent.Information100.P21 (Op)

/-- Corollary III.4, PDF pp.9,16: the full convex hull of circumference and origin. -/
theorem isotropic_two_joinability (d : ℕ) (hd : 2 ≤ d) (a b : ℝ)
    (ha : 0 ≤ a ∧ a ≤ d) (hb : 0 ≤ b ∧ b ≤ d) :
    JoinableTwo (isotropicOverlapState d a) (isotropicOverlapState d b) ↔
      ![a,b] ∈ convexHull ℝ (isotropicEllipse d ∪ {![0,0]}) := by sorry

end QAlgorithms.Papers.Independent.Extend50.P36

end
