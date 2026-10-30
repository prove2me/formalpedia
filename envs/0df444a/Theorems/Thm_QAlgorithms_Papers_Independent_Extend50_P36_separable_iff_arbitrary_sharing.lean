-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Extend50_P36_separable_iff_arbitrary_sharing
-- name    : QAlgorithms.Papers.Independent.Extend50.P36.separable_iff_arbitrary_sharing
-- status  : Open
-- author  : @Gohan
-- created : 2026-10-29T13:54:21.918991+00:00
-- url     : https://prove2.me/theorems/0a35ff90-0937-4adc-a8ee-6e59d1c01c57
-- title:
--   Theorem II.6: separability iff arbitrary sharing
-- statement:
--   For positive integers $m,n$, a state is $m$-$n$ sharable when a density operator on $H_L^{\otimes m}\otimes H_R^{\otimes n}$ has that same state as every left-right pair marginal. Arbitrary sharing means such an extension exists for every positive finite $m,n$.
--
--   For any density operator $\rho$ on nonzero finite-dimensional complex spaces $H_L\otimes H_R$,
--   $$\rho\text{ is separable}\quad\Longleftrightarrow\quad\forall m,n\ge1,\ \rho\text{ is }m\text{-}n\text{ sharable}.$$
--   Separable means a finite convex combination of product density operators. The extension may depend on both sharing counts.
-- source:
--   Compatible quantum correlations: on extension problems for Werner and isotropic states, arXiv:1305.1342v3, PDF p. 5, Theorem II.6: separability iff arbitrary sharing

import Definitions.Def_QAlgorithms_Papers_Independent_Extend50_P36

noncomputable section

open scoped Matrix ComplexConjugate Matrix.Norms.Elementwise

open MeasureTheory

namespace QAlgorithms.Papers.Independent.Extend50.P36

attribute [local instance] Classical.propDecidable Classical.decEq

-- Exact accepted matrix alias; tensor reductions below compose frozen superoperators.

open QAlgorithms.Papers.Independent.Information100.P21 (Op)

/-- Theorem II.6, PDF pp.5–6: finite-dimensional separability iff all finite sharing. -/
theorem separable_iff_arbitrary_sharing {I J : Type*}
    [Fintype I] [Fintype J] [Nonempty I] [Nonempty J]
    (rho : Op (I × J)) (hrho : IsDensityMatrix rho) :
    Entanglement.IsSeparableDensity rho ↔ ArbitrarilySharable rho := by sorry

end QAlgorithms.Papers.Independent.Extend50.P36

end
