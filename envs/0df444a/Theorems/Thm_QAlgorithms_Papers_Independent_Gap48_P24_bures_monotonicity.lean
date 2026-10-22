-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Gap48_P24_bures_monotonicity
-- name    : QAlgorithms.Papers.Independent.Gap48.P24.bures_monotonicity
-- status  : Proved
-- author  : @Goku
-- created : 2026-10-21T22:32:31.179508+00:00
-- url     : https://prove2.me/theorems/010269ce-b83e-4b00-9a79-abb709e73b87
-- title:
--   Monotonicity under precomposition and postcomposition
-- statement:
--   Let $A,B$ be unital complex C*-algebras and $T_1,T_2:A\to B$ bounded completely positive maps, with no normalization or normality condition. The intrinsic distance $\beta_{\rm int}(T_1,T_2)$ is the infimum of $\|\widehat T_{11}(1_A)+\widehat T_{22}(1_A)-\widehat T_{12}(1_A)-\widehat T_{21}(1_A)\|^{1/2}$ over completely positive maps $\widehat T:A\to M_2(B)$ with diagonal entries $T_1,T_2$. All matrix algebras carry their C*-operator norms; $\|\cdot\|_{\rm cb}$ denotes the supremum of all finite amplification norms.
--
--   Let $D$ be another unital complex C*-algebra. For every bounded CP map $S:B\to D$,
--   $$\beta_{\rm int}(S\circ T_1,S\circ T_2)\le\sqrt{\|S\|}\,\beta_{\rm int}(T_1,T_2).$$
--   Independently, for every bounded CP map $S:D\to A$,
--   $$\beta_{\rm int}(T_1\circ S,T_2\circ S)\le\sqrt{\|S\|}\,\beta_{\rm int}(T_1,T_2).$$
--   Here $\|S\|$ is the ordinary operator norm, and $S$ need not be contractive. These estimates describe the behavior of the intrinsic distance under arbitrary CP processing.
-- source:
--   A Continuity Theorem for Stinespring's Dilation, arXiv:0710.2495v1, PDF p. 12, Proposition 8, (33)–(34)

import Definitions.Def_QAlgorithms_Papers_Independent_Gap48_P24

noncomputable section

open scoped ComplexOrder

namespace QAlgorithms.Papers.Independent.Gap48.P24

universe u v

attribute [local instance] Classical.propDecidable

attribute [local instance] Classical.decEq

/-- Proposition 8, PDF pp.12–13, (33)–(34): both composition directions, with
sqrt of the ordinary operator norm and independently quantified composing maps. -/
theorem bures_monotonicity {A B D : Type u}
    [CStarAlgebra A] [PartialOrder A] [StarOrderedRing A] [CStarAlgebra B] [PartialOrder B] [StarOrderedRing B] [CStarAlgebra D] [PartialOrder D] [StarOrderedRing D]
    (T1 T2 : A →L[ℂ] B) (h1 : IsCStarCompletelyPositive T1) (h2 : IsCStarCompletelyPositive T2) :
    (∀ S : B →L[ℂ] D, IsCStarCompletelyPositive S →
      intrinsicBures (S.comp T1) (S.comp T2) ≤ Real.sqrt ‖S‖ * intrinsicBures T1 T2) ∧
    (∀ S : D →L[ℂ] A, IsCStarCompletelyPositive S →
      intrinsicBures (T1.comp S) (T2.comp S) ≤ Real.sqrt ‖S‖ * intrinsicBures T1 T2) := by sorry

end QAlgorithms.Papers.Independent.Gap48.P24

end
