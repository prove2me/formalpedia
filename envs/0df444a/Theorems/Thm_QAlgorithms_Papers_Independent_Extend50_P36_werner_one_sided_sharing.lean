-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Extend50_P36_werner_one_sided_sharing
-- name    : QAlgorithms.Papers.Independent.Extend50.P36.werner_one_sided_sharing
-- status  : Open
-- author  : @Gohan
-- created : 2026-10-29T13:58:32.812035+00:00
-- url     : https://prove2.me/theorems/a34a4569-9081-44d0-8f55-de613f480aa9
-- title:
--   Theorem III.7: exact Werner 1-n sharing
-- statement:
--   Let $d\ge2$ be an integer. Write $\rho_W(\psi)$ for the $d$-dimensional Werner state with swap expectation $\psi\in[-1,1]$, and $\rho_I(\phi)$ for the isotropic state with $\phi=dF\in[0,d]$, where $F$ is its overlap with the normalized maximally entangled vector. A joining state is a positive semidefinite operator of trace one having the specified ordered pair marginals.For positive integers $m,n$, a state is $m$-$n$ sharable when a density operator on $H_L^{\otimes m}\otimes H_R^{\otimes n}$ has that same state as every left-right pair marginal. Arbitrary sharing means such an extension exists for every positive finite $m,n$.
--
--   For every positive integer $n$ and every physical Werner parameter $\psi$,
--   $$\rho_W(\psi)\text{ is }1\text{-}n\text{ sharable}\quad\Longleftrightarrow\quad\psi\ge-\frac{d-1}{n}.$$
--   When $n<d-1$, all physical Werner parameters satisfy the inequality; this regime remains included.
-- source:
--   Compatible quantum correlations: on extension problems for Werner and isotropic states, arXiv:1305.1342v3, PDF p. 11, Theorem III.7: exact Werner 1-n sharing

import Definitions.Def_QAlgorithms_Papers_Independent_Extend50_P36

noncomputable section

open scoped Matrix ComplexConjugate Matrix.Norms.Elementwise

open MeasureTheory

namespace QAlgorithms.Papers.Independent.Extend50.P36

attribute [local instance] Classical.propDecidable Classical.decEq

-- Exact accepted matrix alias; tensor reductions below compose frozen superoperators.

open QAlgorithms.Papers.Independent.Information100.P21 (Op)

/-- Theorem III.7, PDF p.11, repeated as Eq.(B4), PDF p.18:
no additional n >= d-1 restriction is imposed. -/
theorem werner_one_sided_sharing (d n : ℕ) (hd : 2 ≤ d) (hn : 0 < n)
    (psi : ℝ) (hpsi : -1 ≤ psi ∧ psi ≤ 1) :
    Sharable 1 n (wernerSwapState d psi) ↔ -((d : ℝ)-1)/(n : ℝ) ≤ psi := by sorry

end QAlgorithms.Papers.Independent.Extend50.P36

end
