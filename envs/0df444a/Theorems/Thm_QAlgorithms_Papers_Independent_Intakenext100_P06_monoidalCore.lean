-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Intakenext100_P06_monoidalCore
-- name    : QAlgorithms.Papers.Independent.Intakenext100.P06.monoidalCore
-- status  : Open
-- author  : @Gohan
-- created : 2026-10-30T22:52:52.947996+00:00
-- url     : https://prove2.me/theorems/f98f7d47-bee6-4704-8e40-b3b15f526a4f
-- title:
--   The invertible core of a monoidal category is a Gr-category
-- statement:
--   Let $\mathcal M$ be any monoidal category. Form $\mathcal K$ whose objects are the actual objects $x$ having some two-sided weak tensor inverse and whose arrows are precisely the isomorphisms in $\mathcal M$ between these objects, composed as actual isomorphisms. Then
--
--   $$
--   \mathcal K\text{ inherits a monoidal structure from }\mathcal M
--   \quad\text{and is a Gr-category}.
--   $$
--
--   Its forgetful functor is strong monoidal with identity unit and tensor comparisons after endpoint equality. These comparisons also identify the inherited associator and unitors through the full monoidal functor laws. Noninvertible ambient arrows are excluded, and the ambient category need not be a groupoid.
--
--   This supplies exactly the invertible-object core used in the examples.
-- source:
--   Hoàng Xuân Sính's Thesis: Categorifying Group Theory, arXiv:2308.05119v2, PDF p. 11, §5: invertible core is a Gr-category

import Definitions.Def_QAlgorithms_Papers_Independent_Intakenext100_P06

namespace QAlgorithms.Papers.Independent.Intakenext100.P06

open CategoryTheory CategoryTheory.MonoidalCategory

open QAlgorithms.Papers.Independent.Gap48.P14

open QAlgorithms.Papers.Independent.Renew46.P18

universe u v u1 v1 w

attribute [local instance] QAlgorithms.Papers.Independent.Intakenext100.P06.singletonSymmetric

/-- Section 5, PDF p. 11: the invertible core inherits the ambient
monoidal structure with identity comparison maps (up to endpoint equality).
The strong-monoidal laws therefore also identify all inherited coherence.
No invertibility condition is imposed on arbitrary ambient arrows. -/
theorem monoidalCore {C : Type u} [Category.{v} C] [MonoidalCategory C] :
    ∃ m : MonoidalCategory (CoreObjects C),
      letI := m
      ∃ q : (coreForget (C := C)).Monoidal,
        letI := q
        IsWeakTwoGroup (CoreObjects C) ∧
        (∀ x y : CoreObjects C,
          ∃ p : x.val ⊗ y.val = (x ⊗ y).val,
            Functor.LaxMonoidal.μ (coreForget (C := C)) x y = eqToHom p) ∧
        (∃ p : (𝟙_ C) = (𝟙_ (CoreObjects C)).val,
          Functor.LaxMonoidal.ε (coreForget (C := C)) = eqToHom p) := by sorry

end QAlgorithms.Papers.Independent.Intakenext100.P06
