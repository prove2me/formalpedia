-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Extend50_P36_isotropic_one_sided_sharing
-- name    : QAlgorithms.Papers.Independent.Extend50.P36.isotropic_one_sided_sharing
-- status  : Open
-- author  : @Gohan
-- created : 2026-10-29T13:59:14.64319+00:00
-- url     : https://prove2.me/theorems/3cef1b74-cc2c-49f1-a60c-9d1f067c25ad
-- title:
--   Theorem III.8: exact isotropic 1-n sharing
-- statement:
--   Let $d\ge2$ be an integer. Write $\rho_W(\psi)$ for the $d$-dimensional Werner state with swap expectation $\psi\in[-1,1]$, and $\rho_I(\phi)$ for the isotropic state with $\phi=dF\in[0,d]$, where $F$ is its overlap with the normalized maximally entangled vector. A joining state is a positive semidefinite operator of trace one having the specified ordered pair marginals.For positive integers $m,n$, a state is $m$-$n$ sharable when a density operator on $H_L^{\otimes m}\otimes H_R^{\otimes n}$ has that same state as every left-right pair marginal. Arbitrary sharing means such an extension exists for every positive finite $m,n$.
--
--   For every positive integer $n$ and every $\phi\in[0,d]$,
--   $$\rho_I(\phi)\text{ is }1\text{-}n\text{ sharable}\quad\Longleftrightarrow\quad\phi\le1+\frac{d-1}{n}.$$
--   The separable endpoint $\phi=0$ is included, as is the whole physical interval for $n=1$.
-- source:
--   Compatible quantum correlations: on extension problems for Werner and isotropic states, arXiv:1305.1342v3, PDF p. 11, Theorem III.8: exact isotropic 1-n sharing

import Definitions.Def_QAlgorithms_Papers_Independent_Extend50_P36

noncomputable section

open scoped Matrix ComplexConjugate Matrix.Norms.Elementwise

open MeasureTheory

namespace QAlgorithms.Papers.Independent.Extend50.P36

attribute [local instance] Classical.propDecidable Classical.decEq

-- Exact accepted matrix alias; tensor reductions below compose frozen superoperators.

open QAlgorithms.Papers.Independent.Information100.P21 (Op)

/-- Theorem III.8, PDF p.11: includes the zero isotropic endpoint. -/
theorem isotropic_one_sided_sharing (d n : ℕ) (hd : 2 ≤ d) (hn : 0 < n)
    (phi : ℝ) (hphi : 0 ≤ phi ∧ phi ≤ d) :
    Sharable 1 n (isotropicOverlapState d phi) ↔ phi ≤ 1+((d : ℝ)-1)/(n : ℝ) := by sorry

end QAlgorithms.Papers.Independent.Extend50.P36

end
