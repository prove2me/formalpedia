-- Prove2me | Theorems.Thm_PretorsionImageClosed_LinearQuiver_canonicalHom_le_rfl_eq_intervalIncl
-- name    : PretorsionImageClosed.LinearQuiver.canonicalHom_le_rfl_eq_intervalIncl
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-25T03:13:01.543928+00:00
-- url     : https://prove2.me/theorems/7cd38359-1637-4281-8bae-3da54a17dc68
-- title:
--   Linear Quiver: canonical Hom le rfl eq interval Incl
-- statement:
--   The Linear Quiver construction uses the canonical Hom le rfl eq interval Incl property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/haruhisa-enomoto/pretorsion-image-closed/blob/e803b5d1325bc1ce2b779efbff157b6cd3234bc8/PretorsionImageClosed/LinearQuiver/Subobjects.lean#L231-L233
-- source:
--   https://github.com/haruhisa-enomoto/pretorsion-image-closed/blob/e803b5d1325bc1ce2b779efbff157b6cd3234bc8/PretorsionImageClosed/LinearQuiver/Subobjects.lean#L231-L233

module
public import Definitions.Def_PretorsionImageClosed_LinearQuiver_Indecomposables
public import Definitions.Def_PretorsionImageClosed_Subcategories_Trace
public import Definitions.Def_PretorsionImageClosed_LinearQuiver_Subobjects
set_option autoImplicit true
@[expose] public section
public section
set_option autoImplicit false
noncomputable section
open PretorsionImageClosed
open CategoryTheory Limits Statement
open PretorsionImageClosed.LinearQuiver
universe u
variable {k : Type u} [Field k] {n : ℕ}

theorem PretorsionImageClosed.LinearQuiver.canonicalHom_le_rfl_eq_intervalIncl {a c d : Fin n} (hac : a ≤ c) :
    canonicalHom (k := k) hac (le_refl d) = intervalIncl k d hac := by sorry
