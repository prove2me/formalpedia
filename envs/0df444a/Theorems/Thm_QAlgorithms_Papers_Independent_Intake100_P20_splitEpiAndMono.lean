-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Intake100_P20_splitEpiAndMono
-- name    : QAlgorithms.Papers.Independent.Intake100.P20.splitEpiAndMono
-- status  : Open
-- author  : @Gohan
-- created : 2026-10-30T16:32:26.477121+00:00
-- url     : https://prove2.me/theorems/d016e849-2e4e-4e41-b785-f1fad0193d87
-- title:
--   A split epimorphism has a monic section
-- statement:
--   In any category, let $s:A\to O$ and $e:O\to A$ satisfy $s\circ e=\mathrm{id}_O$. Then
--
--   $$s\text{ is an epimorphism},\qquad e\text{ is a monomorphism}.$$
--
--   No property of groups is needed. This abstracts the split source and identity maps used later for internal categories.
-- source:
--   Group Objects and Internal Categories, arXiv:math/0212065v1, PDF p. 8, §3, Interlude, pp. 8–9

import Definitions.Def_QAlgorithms_Papers_Independent_Intake100_P20

namespace QAlgorithms.Papers.Independent.Intake100.P20

open CategoryTheory

open scoped TensorProduct Manifold ContDiff

universe u v w z

/-- PDF pp. 8–9, Interlude: a splitting is epi and its section is mono
in ANY category. Lean's composition e ≫ s is the source's s after e. -/
theorem splitEpiAndMono {C : Type u} [Category.{v} C] {A O : C}
    (s : A ⟶ O) (e : O ⟶ A) (h : e ≫ s = 𝟙 O) :
    Epi s ∧ Mono e := by sorry

end QAlgorithms.Papers.Independent.Intake100.P20
