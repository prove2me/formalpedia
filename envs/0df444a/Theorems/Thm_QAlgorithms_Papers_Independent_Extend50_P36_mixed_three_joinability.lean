-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Extend50_P36_mixed_three_joinability
-- name    : QAlgorithms.Papers.Independent.Extend50.P36.mixed_three_joinability
-- status  : Open
-- author  : @Gohan
-- created : 2026-10-29T13:55:32.347989+00:00
-- url     : https://prove2.me/theorems/59f45a98-861e-4ae8-9eef-13d09a1015a6
-- title:
--   Theorem III.2: isotropic-isotropic-Werner triple
-- statement:
--   Let $d\ge2$ be an integer. Write $\rho_W(\psi)$ for the $d$-dimensional Werner state with swap expectation $\psi\in[-1,1]$, and $\rho_I(\phi)$ for the isotropic state with $\phi=dF\in[0,d]$, where $F$ is its overlap with the normalized maximally entangled vector. A joining state is a positive semidefinite operator of trace one having the specified ordered pair marginals.
--
--   Set $a=\phi_{AB},b=\phi_{AC},c=\psi_{BC}$ and $\eta=\sqrt{(d-1)/(2d)}+i\sqrt{(d+1)/(2d)}$. Let $K_d$ be the subset of the physical parameter box satisfying
--   $$a+b-c\le d,\qquad |d(c-1)+\sqrt{2d/(d-1)}(\eta a+\overline\eta b)|\le1+a+b-c.$$
--   The isotropic AB and AC states and Werner BC state are joinable exactly when $(a,b,c)\in K_2$ for $d=2$, or $(a,b,c)\in\operatorname{conv}(K_d\cup\{(0,0,-1)\})$ for $d\ge3$.
--
--   This gives the exact mixed three-pair region.
-- source:
--   Compatible quantum correlations: on extension problems for Werner and isotropic states, arXiv:1305.1342v3, PDF p. 8, Theorem III.2: isotropic-isotropic-Werner triple

import Definitions.Def_QAlgorithms_Papers_Independent_Extend50_P36

noncomputable section

open scoped Matrix ComplexConjugate Matrix.Norms.Elementwise

open MeasureTheory

namespace QAlgorithms.Papers.Independent.Extend50.P36

attribute [local instance] Classical.propDecidable Classical.decEq

-- Exact accepted matrix alias; tensor reductions below compose frozen superoperators.

open QAlgorithms.Papers.Independent.Information100.P21 (Op)

/-- Theorem III.2, PDF pp.8,15–16: two isotropic pairs AB,AC and a Werner pair BC. -/
theorem mixed_three_joinability (d : ℕ) (hd : 2 ≤ d) (a b c : ℝ)
    (ha : 0 ≤ a ∧ a ≤ d) (hb : 0 ≤ b ∧ b ≤ d) (hc : -1 ≤ c ∧ c ≤ 1) :
    JoinableThree (isotropicOverlapState d a) (isotropicOverlapState d b) (wernerSwapState d c) ↔
      ![a,b,c] ∈ mixedRegion d := by sorry

end QAlgorithms.Papers.Independent.Extend50.P36

end
