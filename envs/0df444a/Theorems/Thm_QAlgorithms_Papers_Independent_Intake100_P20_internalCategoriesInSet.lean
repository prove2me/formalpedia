-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Intake100_P20_internalCategoriesInSet
-- name    : QAlgorithms.Papers.Independent.Intake100.P20.internalCategoriesInSet
-- status  : Open
-- author  : @Gohan
-- created : 2026-10-30T16:31:15.413147+00:00
-- url     : https://prove2.me/theorems/d2cec87a-6672-4b67-a991-f6d953672f31
-- title:
--   Internal categories in Set are ordinary small categories
-- statement:
--   An internal category in Set has an object set $O$, an arrow set $A$, source and target maps $s,t:A\to O$, identities $e:O\to A$, and composition $g\circ f$ when $t(f)=s(g)$. Require $se=te=\mathrm{id}_O$, the correct source and target of a composite, associativity, and both unit laws. It gives an ordinary small category by
--
--   $$\operatorname{Hom}(x,y)=\{f\in A:s(f)=x,\ t(f)=y\}.$$
--
--   Conversely, the total arrow set $\coprod_{x,y}\operatorname{Hom}(x,y)$ of an ordinary small category has these internal maps, with $(y,z,g)\circ(x,y,f)=(x,z,f\mathbin{;}g)$, where $f\mathbin{;}g$ means first $f$, then $g$. The explicit arrow and hom-fibre equivalences recover identities and composition. Empty categories are allowed. This is a correspondence of structures with the original operations, not two unrelated existence statements.
-- source:
--   Group Objects and Internal Categories, arXiv:math/0212065v1, PDF p. 8, §3, pp. 6–8

import Definitions.Def_QAlgorithms_Papers_Independent_Intake100_P20

namespace QAlgorithms.Papers.Independent.Intake100.P20

open CategoryTheory

open scoped TensorProduct Manifold ContDiff

universe u v w z

/-- PDF pp. 6–8: internal categories in Set and ordinary small categories have
mutually inverse structure translations. Objects stay fixed; arrows are identified
by the displayed canonical equivalences. Every reconstruction equation for
composition is restricted to the source's composable pairs. -/
theorem internalCategoriesInSet :
    (∀ {A : Type u} {O : Type v} (D : CategoryMaps A O) (h : CategoryDiagrams D),
      letI := categoryOfMaps D h
      let E := mapsOfCategory O
      let q := totalArrowEquiv D h
      (∀ a, E.source (q a) = D.source a ∧ E.target (q a) = D.target a) ∧
      (∀ x, E.identity x = q (D.identity x)) ∧
      (∀ f g, D.target f = D.source g →
        E.compose (q g) (q f) = q (D.compose g f))) ∧
    (∀ (O : Type v) [Category.{u} O], CategoryDiagrams (mapsOfCategory O) ∧
      (∀ x, (mapsOfCategory O).identity x = ⟨x, x, 𝟙 x⟩) ∧
      (∀ x y z (f : x ⟶ y) (g : y ⟶ z),
        (mapsOfCategory O).compose ⟨y, z, g⟩ ⟨x, y, f⟩ = ⟨x, z, f ≫ g⟩) ∧
      (∀ x y (f : x ⟶ y), (totalHomEquiv O x y f).val = ⟨x, y, f⟩)) := by sorry

end QAlgorithms.Papers.Independent.Intake100.P20
