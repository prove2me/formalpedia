-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Extend50_P36_werner_three_joinability
-- name    : QAlgorithms.Papers.Independent.Extend50.P36.werner_three_joinability
-- status  : Open
-- author  : @Gohan
-- created : 2026-10-29T13:51:12.017531+00:00
-- url     : https://prove2.me/theorems/a11e1d18-2c90-4ee3-a797-591be95575e1
-- title:
--   Theorem III.1: three Werner marginals (original paper seed)
-- statement:
--   Let $d\ge2$ be an integer. Write $\rho_W(\psi)$ for the $d$-dimensional Werner state with swap expectation $\psi\in[-1,1]$, and $\rho_I(\phi)$ for the isotropic state with $\phi=dF\in[0,d]$, where $F$ is its overlap with the normalized maximally entangled vector. A joining state is a positive semidefinite operator of trace one having the specified ordered pair marginals.
--
--   Put $a=\psi_{AB}$, $b=\psi_{AC}$, $c=\psi_{BC}$, $\mu=(a+b+c)/3$, and $\omega=e^{2\pi i/3}$. The three states are joinable precisely when
--   $$
--   \frac23|c+\omega b+\omega^2a|\le1-\mu,\qquad
--   \begin{cases}\mu\ge0,&d=2,\\ \frac23|c+\omega b+\omega^2a|\le1+\mu,&d\ge3.\end{cases}
--   $$
--   This is the exact three-Werner compatibility region.
-- source:
--   Compatible quantum correlations: on extension problems for Werner and isotropic states, arXiv:1305.1342v3, PDF p. 8, Theorem III.1: three Werner marginals (original paper seed)

import Definitions.Def_QAlgorithms_Papers_Independent_Extend50_P36

noncomputable section

open scoped Matrix ComplexConjugate Matrix.Norms.Elementwise

open MeasureTheory

namespace QAlgorithms.Papers.Independent.Extend50.P36

attribute [local instance] Classical.propDecidable Classical.decEq

-- Exact accepted matrix alias; tensor reductions below compose frozen superoperators.

open QAlgorithms.Papers.Independent.Information100.P21 (Op)

/-- Theorem III.1, PDF pp.8,15: complete Werner triple criterion, with the
additional mean constraint in dimension two. -/
theorem werner_three_joinability (d : ℕ) (hd : 2 ≤ d) (a b c : ℝ)
    (ha : -1 ≤ a ∧ a ≤ 1) (hb : -1 ≤ b ∧ b ≤ 1) (hc : -1 ≤ c ∧ c ≤ 1) :
    JoinableThree (wernerSwapState d a) (wernerSwapState d b) (wernerSwapState d c) ↔ wernerRegion d a b c := by sorry

end QAlgorithms.Papers.Independent.Extend50.P36

end
