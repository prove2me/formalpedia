-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Intake100_P16_monoidalDelooping
-- name    : QAlgorithms.Papers.Independent.Intake100.P16.monoidalDelooping
-- status  : Open
-- author  : @Gohan
-- created : 2026-10-30T13:19:52.072813+00:00
-- url     : https://prove2.me/theorems/7312a0f7-154f-4f06-8955-7daa8dd5d8f3
-- title:
--   Example A.2: monoidal categories as single-object bicategories
-- statement:
--   Let $C$ be a monoidal category with tensor unit $I$, associator $\alpha$, and invertible unitors satisfying the usual coherence laws. There is a bicategory $BC$ with one object. Its 1-morphisms are the objects of $C$, and its 2-morphisms are the morphisms of $C$. In the paper's composition order,
--   $$
--   g\circ f=g\otimes f,\qquad a_{f,g,h}=\alpha_{h,g,f},\qquad \mathrm{id}_*=I.
--   $$
--   Horizontal composition is tensor product, vertical composition and identity 2-morphisms are those of $C$, and the unitors are the given monoidal unitors, matched to their source and target. These data satisfy the bicategory axioms. Moreover,
--   $$
--   BC\text{ is strict}\quad\Longleftrightarrow\quad C\text{ is strict as the specified monoidal category}.
--   $$
--   Strictness here requires the tensor to be associative and unital as equalities, and the given associator and unitors to be identity morphisms under those equalities. It does not mean merely equivalence to a strict monoidal category.
--
--   This construction translates monoidal categories into the 2-categorical language used for target bicategories.
--
--   **Formalization Note** The 1-cell opposite of Mathlib's monoidal delooping supplies the source order without assuming a braiding. Mathlib's inverse bicategory associator is the paper's forward associator.
-- source:
--   Local Theory for 2-Functors on Path 2-Groupoids, arXiv:1303.4663v1, PDF p. 39, A.2

import Definitions.Def_QAlgorithms_Papers_Independent_Intake100_P16

namespace QAlgorithms.Papers.Independent.Intake100.P16

open CategoryTheory CategoryTheory.Bicategory CategoryTheory.MonoidalCategory

open scoped CategoryTheory.Pseudofunctor.StrongTrans

universe uS vS wS uT vT wT uC vC

/-- Example A.2, PDF pp.39–40. The specified delooping is a bicategory,
with tensor composition, the source's alpha_{Z,Y,X}, the corresponding
unitors, and the original category's vertical composition and identities.
It is strict exactly when the given monoidal structure is strict.
The inverse Mathlib bicategory associator is the paper's forward associator. -/
theorem monoidalDelooping
    (C : Type uC) [Category.{vC} C] [MonoidalCategory C] :
    Nonempty (Bicategory (PaperDelooping C)) ∧
    (∀ a b : PaperDelooping C, a = b) ∧
    (∀ a : PaperDelooping C, ((𝟙 a : a ⟶ a).unop : C) = 𝟙_ C) ∧
    (∀ {a b c : PaperDelooping C} (f : a ⟶ b) (g : b ⟶ c),
      (f ≫ g).unop = g.unop ⊗ f.unop) ∧
    (∀ {a b c d : PaperDelooping C} (f : a ⟶ b) (g : b ⟶ c) (h : c ⟶ d),
      ((Bicategory.associator f g h).inv).unop2 = (MonoidalCategory.associator h.unop g.unop f.unop).hom) ∧
    (∀ {a b : PaperDelooping C} (f : a ⟶ b),
      ((Bicategory.leftUnitor f).hom).unop2 = (MonoidalCategory.rightUnitor f.unop).hom ∧
      ((Bicategory.rightUnitor f).hom).unop2 = (MonoidalCategory.leftUnitor f.unop).hom) ∧
    (∀ {a b : PaperDelooping C} {f g h : a ⟶ b} (e : f ⟶ g) (z : g ⟶ h),
      (e ≫ z).unop2 = e.unop2 ≫ z.unop2) ∧
    (∀ {a b : PaperDelooping C} (f : a ⟶ b),
      Bicategory.Opposite.Hom2.unop2 (𝟙 f : f ⟶ f) = 𝟙 f.unop) ∧
    (∀ {a b c : PaperDelooping C} {f fnew : a ⟶ b} {g gnew : b ⟶ c}
      (e : f ⟶ fnew) (z : g ⟶ gnew),
      ((e ▷ g) ≫ (fnew ◁ z)).unop2 = z.unop2 ⊗ₘ e.unop2) ∧
    (Bicategory.Strict (PaperDelooping C) ↔ IsStrictMonoidal C) := by sorry

end QAlgorithms.Papers.Independent.Intake100.P16
