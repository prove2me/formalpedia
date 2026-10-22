-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Gap48_P14_oneSidedInverses_suffice
-- name    : QAlgorithms.Papers.Independent.Gap48.P14.oneSidedInverses_suffice
-- status  : Proved
-- author  : @Goku
-- created : 2026-10-21T21:48:46.153306+00:00
-- url     : https://prove2.me/theorems/77946d23-3017-4c6e-ac1b-2dbcc46c6644
-- title:
--   Universal one-sided inverses suffice
-- statement:
--   Throughout, categories and morphisms lie in fixed universes, and composition is written in order of application. Let $C$ be a monoidal category and suppose every object has a left weak inverse: for every $x$ there is $y$ with $y\otimes x\cong1$. Then
--   $$\forall x\in C\;\exists y\in C:\quad x\otimes y\cong1\quad\text{and}\quad y\otimes x\cong1.$$
--   No invertibility assumption is placed on arbitrary arrows. This replaces the two-sided object-invertibility requirement by universal one-sided invertibility.
-- source:
--   Higher-Dimensional Algebra V: 2-Groups, arXiv:math/0307200v3, PDF p. 8, Section 2: one-sided weak inverses suffice

import Definitions.Def_QAlgorithms_Papers_Independent_Gap48_P14

namespace QAlgorithms.Papers.Independent.Gap48.P14

open CategoryTheory CategoryTheory.MonoidalCategory

universe u v u1 v1

section Inverses

variable {C : Type u} [Category.{v} C] [MonoidalCategory C]

/-- Section 2, PDF p. 8: universal existence of left weak inverses forces
all the objects to have two-sided weak inverses. No groupoid assumption. -/
theorem oneSidedInverses_suffice
    (h : ∀ x : C, ∃ y : C, Nonempty (y ⊗ x ≅ 𝟙_ C)) :
    ∀ x : C, ∃ y : C, IsWeakInverse x y := by sorry

end Inverses

end QAlgorithms.Papers.Independent.Gap48.P14
