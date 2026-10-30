-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Extend50_P36_one_sided_arbitrary_implies_arbitrary
-- name    : QAlgorithms.Papers.Independent.Extend50.P36.one_sided_arbitrary_implies_arbitrary
-- status  : Open
-- author  : @Gohan
-- created : 2026-10-29T14:03:21.950308+00:00
-- url     : https://prove2.me/theorems/6344b0a4-35e0-4745-9449-f43099c0e752
-- title:
--   Sec. II B, unnumbered corollary: one-sided arbitrary sharing suffices
-- statement:
--   For positive integers $m,n$, a state is $m$-$n$ sharable when a density operator on $H_L^{\otimes m}\otimes H_R^{\otimes n}$ has that same state as every left-right pair marginal. Arbitrary sharing means such an extension exists for every positive finite $m,n$.
--
--   For a density operator $\rho$ on nonzero finite-dimensional local spaces,
--   $$[\forall n\ge1,\ \rho\text{ is }1\text{-}n\text{ sharable}]\quad\Longrightarrow\quad[\forall m,n\ge1,\ \rho\text{ is }m\text{-}n\text{ sharable}].$$
--   No infinite tensor-product operator or single finite sharing count is asserted.
-- source:
--   Compatible quantum correlations: on extension problems for Werner and isotropic states, arXiv:1305.1342v3, PDF p. 6, Sec. II B, unnumbered corollary: one-sided arbitrary sharing suffices

import Definitions.Def_QAlgorithms_Papers_Independent_Extend50_P36

noncomputable section

open scoped Matrix ComplexConjugate Matrix.Norms.Elementwise

open MeasureTheory

namespace QAlgorithms.Papers.Independent.Extend50.P36

attribute [local instance] Classical.propDecidable Classical.decEq

-- Exact accepted matrix alias; tensor reductions below compose frozen superoperators.

open QAlgorithms.Papers.Independent.Information100.P21 (Op)

/-- Sec.II B, PDF p.6: one-sided arbitrary finite sharing suffices for arbitrary sharing. -/
theorem one_sided_arbitrary_implies_arbitrary {I J : Type*} [Fintype I] [Fintype J]
    [Nonempty I] [Nonempty J] (rho : Op (I × J)) (hrho : IsDensityMatrix rho)
    (hshare : ∀ n : ℕ, 0 < n → Sharable 1 n rho) : ArbitrarilySharable rho := by sorry

end QAlgorithms.Papers.Independent.Extend50.P36

end
