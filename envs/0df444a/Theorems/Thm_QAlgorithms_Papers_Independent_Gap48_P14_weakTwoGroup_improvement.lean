-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Gap48_P14_weakTwoGroup_improvement
-- name    : QAlgorithms.Papers.Independent.Gap48.P14.weakTwoGroup_improvement
-- status  : Proved
-- author  : @Goku
-- created : 2026-10-21T21:47:09.745688+00:00
-- url     : https://prove2.me/theorems/5854eadf-5d83-41d0-8d7b-620076cfc305
-- title:
--   Improve a weak 2-group on the same monoidal groupoid
-- statement:
--   Throughout, categories and morphisms lie in fixed universes, and composition is written in order of application. Let $C$ be a weak 2-group: a monoidal category with every arrow invertible and every object weakly invertible. Use classical choice to select, for each $x$, a weak inverse $y_x$ and isomorphisms $i_x:1\cong x\otimes y_x$ and $e_x:y_x\otimes x\cong1$. For these choices, define $J_L$ by the following formula with $y=y_x$, $i=i_x$, and $e=e_x$. Put $z=x\otimes y$ and define
--   $$P=i;(1_x\otimes\lambda_y^{-1});(1_x\otimes(e^{-1}\otimes1_y));(1_x\otimes a_{y,x,y});a_{x,y,z}^{-1}.$$
--   The two composites from the unit to $x\otimes y$ are
--   $$J_L=P;(i^{-1}\otimes1_z);a_{1,x,y}^{-1};(\lambda_x\otimes1_y),\qquad J_R=P;(1_z\otimes i^{-1});\rho_z.$$
--   Here $a$, $\lambda$ and $\rho$ are the associator and the left and right unitors, and semicolons denote composition in order of application.
--   There is a coherent 2-group structure on exactly this monoidal category whose specified data obey
--   $$\overline{x}=y_x,\qquad i'_x=J_L(i_x,e_x),\qquad e'_x=e_x.$$
--   In particular both zig-zag identities hold. This adds adjoint-equivalence choices while retaining the underlying weak 2-group.
-- source:
--   Higher-Dimensional Algebra V: 2-Groups, arXiv:math/0307200v3, PDF p. 19, Theorem 14: improve any weak 2-group

import Definitions.Def_QAlgorithms_Papers_Independent_Gap48_P14

namespace QAlgorithms.Papers.Independent.Gap48.P14

open CategoryTheory CategoryTheory.MonoidalCategory

universe u v u1 v1

section Inverses

variable {C : Type u} [Category.{v} C] [MonoidalCategory C]

/-- Theorem 14, PDF pp. 19–24: the selected weak inverses are improved on the
same monoidal groupoid using exactly the p. 19 unit composite and the old counit. -/
theorem weakTwoGroup_improvement (h : IsWeakTwoGroup C) :
    ∃ d : CoherentInverseData C,
      d.toWeakInverseData =
        { inverse := (chosenWeakInverseData h).inverse
          unitIso := fun x => improvedUnitIso
            ((chosenWeakInverseData h).unitIso x) ((chosenWeakInverseData h).counitIso x)
          counitIso := (chosenWeakInverseData h).counitIso } := by sorry

end Inverses

end QAlgorithms.Papers.Independent.Gap48.P14
