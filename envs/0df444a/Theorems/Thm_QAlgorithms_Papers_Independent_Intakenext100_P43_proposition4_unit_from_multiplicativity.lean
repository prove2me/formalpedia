-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Intakenext100_P43_proposition4_unit_from_multiplicativity
-- name    : QAlgorithms.Papers.Independent.Intakenext100.P43.proposition4_unit_from_multiplicativity
-- status  : Open
-- author  : @Gohan
-- created : 2026-10-31T05:49:34.68782+00:00
-- url     : https://prove2.me/theorems/67f6cc24-ccfd-442e-b09c-d6ffd359d2d7
-- title:
--   Multiplicative transition maps have the diagonal unit law
-- statement:
--   Let $\mathcal C$ have finite products and a specified class of covers satisfying the five axioms of §1.1.5: isomorphisms and composites are covers, covers have stable pullbacks, covered equivalence relations have covering quotients, and every cover is the quotient of its kernel pair. Let $j:U\to B$ be a cover with specified kernel pair $U^{[2]}$ and triple pullback $U^{[3]}$, and let $G$ be an internal group. A map $g:U^{[2]}\to G$ satisfying $g_{xy}g_{yz}=g_{xz}$ also satisfies
--
--   $$g_{xx}=1_G.$$
--
--   Here the notation denotes generalized elements, so the conclusion is equality of maps $U\to G$. The unit law is a conclusion, not part of the transition data assumed in the premise.
-- source:
--   Higher gauge theory I: 2-Bundles, arXiv:math/0410328v3, PDF p. 18, Proposition 4

import Definitions.Def_QAlgorithms_Papers_Independent_Intakenext100_P43

namespace QAlgorithms.Papers.Independent.Intakenext100.P43

open CategoryTheory CategoryTheory.Limits

open CategoryTheory.MonoidalCategory CategoryTheory.CartesianMonoidalCategory

universe u v w

section Ordinary

variable {C : Type u} [Category.{v} C]

variable [CartesianMonoidalCategory C]

/-- Proposition 4, PDF p. 18: multiplicativity implies the diagonal
unit law. The input is a raw map satisfying gamma, not a transition
data that already includes eta. The five cover axioms are explicit. -/
theorem proposition4_unit_from_multiplicativity
    (S : CoverTheory (C := C)) {U B : C} (j : U ⟶ B)
    (hj : S.covers j) (K : CechData j) (G : C) [GrpObj G]
    (g : K.pairSpace ⟶ G) (hgamma : SatisfiesGamma K G g) :
    cechDiagonal K ≫ g = toUnit U ≫ MonObj.one (X := G) := by sorry

end Ordinary

end QAlgorithms.Papers.Independent.Intakenext100.P43
