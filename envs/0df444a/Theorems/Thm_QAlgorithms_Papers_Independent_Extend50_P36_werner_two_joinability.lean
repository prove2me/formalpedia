-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Extend50_P36_werner_two_joinability
-- name    : QAlgorithms.Papers.Independent.Extend50.P36.werner_two_joinability
-- status  : Open
-- author  : @Gohan
-- created : 2026-10-29T13:56:09.600961+00:00
-- url     : https://prove2.me/theorems/db8cb055-7c2a-4581-9f25-a84e106fb8a2
-- title:
--   Corollary III.3: two Werner marginals
-- statement:
--   Let $d\ge2$ be an integer. Write $\rho_W(\psi)$ for the $d$-dimensional Werner state with swap expectation $\psi\in[-1,1]$, and $\rho_I(\phi)$ for the isotropic state with $\phi=dF\in[0,d]$, where $F$ is its overlap with the normalized maximally entangled vector. A joining state is a positive semidefinite operator of trace one having the specified ordered pair marginals.
--
--   For $a,b\in[-1,1]$, the Werner AB and AC states are joinable if and only if
--   $$
--   (a\ge-\tfrac12\ \land\ b\ge-\tfrac12)\ \lor\ (a+b)^2+\tfrac13(a-b)^2\le1\ \lor\ (d\ge3\ \land\ a\le\tfrac12\ \land\ b\le\tfrac12).
--   $$
--   The rectangles and the filled ellipse together give the exact projected region.
-- source:
--   Compatible quantum correlations: on extension problems for Werner and isotropic states, arXiv:1305.1342v3, PDF p. 9, Corollary III.3: two Werner marginals

import Definitions.Def_QAlgorithms_Papers_Independent_Extend50_P36

noncomputable section

open scoped Matrix ComplexConjugate Matrix.Norms.Elementwise

open MeasureTheory

namespace QAlgorithms.Papers.Independent.Extend50.P36

attribute [local instance] Classical.propDecidable Classical.decEq

-- Exact accepted matrix alias; tensor reductions below compose frozen superoperators.

open QAlgorithms.Papers.Independent.Information100.P21 (Op)

/-- Corollary III.3, PDF pp.9,16: both rectangular coordinates obey each bound;
the ellipse has coefficient 1/3 on the squared difference. -/
theorem werner_two_joinability (d : ℕ) (hd : 2 ≤ d) (a b : ℝ)
    (ha : -1 ≤ a ∧ a ≤ 1) (hb : -1 ≤ b ∧ b ≤ 1) :
    JoinableTwo (wernerSwapState d a) (wernerSwapState d b) ↔
      (-1/2 ≤ a ∧ -1/2 ≤ b) ∨ (a+b)^2+(1/3 : ℝ)*(a-b)^2 ≤ 1 ∨
      (3 ≤ d ∧ a ≤ 1/2 ∧ b ≤ 1/2) := by sorry

end QAlgorithms.Papers.Independent.Extend50.P36

end
