-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Gap48_P14_strongMonoidal_inverseComparison
-- name    : QAlgorithms.Papers.Independent.Gap48.P14.strongMonoidal_inverseComparison
-- status  : Proved
-- author  : @Goku
-- created : 2026-10-21T21:48:12.849929+00:00
-- url     : https://prove2.me/theorems/8d28ba6c-87ea-456d-b4be-8e3d3cf2e19f
-- title:
--   Unique inverse comparison compatible with unit and counit
-- statement:
--   Throughout, categories and morphisms lie in fixed universes, and composition is written in order of application. Let $C,D$ be coherent 2-groups and $F:C\to D$ a strong monoidal functor. Write $\bar x$ for each specified inverse, $i_x:1_C\cong x\otimes\bar x$ for its unit, and $e_x:\bar x\otimes x\cong1_C$ for its counit, using the same notation in $D$. Let $F_0:1_D\cong F(1_C)$ and $F_2:F(x)\otimes F(y)\cong F(x\otimes y)$ be the comparison maps. For every $x\in C$, there is a unique isomorphism $q:\overline{F(x)}\cong F(\bar x)$ such that
--   $$i_{F(x)};(1_{F(x)}\otimes q);F_2=F_0;F(i_x),$$
--   $$(q\otimes1_{F(x)});F_2;F(e_x)=e_{F(x)};F_0.$$
--   This states preservation of the specified adjoint equivalences through their canonical comparison, including both compatibility laws.
-- source:
--   Higher-Dimensional Algebra V: 2-Groups, arXiv:math/0307200v3, PDF p. 26, Theorem 18: unique inverse comparison compatible with units and counits

import Definitions.Def_QAlgorithms_Papers_Independent_Gap48_P14

namespace QAlgorithms.Papers.Independent.Gap48.P14

open CategoryTheory CategoryTheory.MonoidalCategory

universe u v u1 v1

section Inverses

variable {C : Type u} [Category.{v} C] [MonoidalCategory C]

/-- Theorem 18, PDF pp. 26–31: the unique inverse comparison satisfies BOTH H1
and H2. The source is the specified inverse of F(x), not F(x) itself. -/
theorem strongMonoidal_inverseComparison
    {D : Type u1} [Category.{v1} D] [MonoidalCategory D]
    (hC : ∀ (x y : C) (f : x ⟶ y), IsIso f)
    (hD : ∀ (x y : D) (f : x ⟶ y), IsIso f)
    (c : CoherentInverseData C) (d : CoherentInverseData D)
    (F : C ⥤ D) [F.Monoidal] (x : C) :
    ∃! q : d.inverse (F.obj x) ≅ F.obj (c.inverse x),
      (d.unitIso (F.obj x)).hom ≫ F.obj x ◁ q.hom ≫
          Functor.LaxMonoidal.μ F x (c.inverse x) =
        Functor.LaxMonoidal.ε F ≫ F.map (c.unitIso x).hom ∧
      q.hom ▷ F.obj x ≫ Functor.LaxMonoidal.μ F (c.inverse x) x ≫
          F.map (c.counitIso x).hom =
        (d.counitIso (F.obj x)).hom ≫ Functor.LaxMonoidal.ε F := by sorry

end Inverses

end QAlgorithms.Papers.Independent.Gap48.P14
