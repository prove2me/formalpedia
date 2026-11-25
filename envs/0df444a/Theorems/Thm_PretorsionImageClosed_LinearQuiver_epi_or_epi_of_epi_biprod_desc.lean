-- Prove2me | Theorems.Thm_PretorsionImageClosed_LinearQuiver_epi_or_epi_of_epi_biprod_desc
-- name    : PretorsionImageClosed.LinearQuiver.epi_or_epi_of_epi_biprod_desc
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-25T03:14:01.057697+00:00
-- url     : https://prove2.me/theorems/e10aeb86-e852-4b6e-ad86-9e8f4bfd248e
-- title:
--   Linear Quiver: epi or epi of epi biprod desc
-- statement:
--   Lemma 5.3(1): if `M_{a,d}` is a quotient of `Y₁ ⊞ Y₂`, it is a quotient of `Y₁` or
--   of `Y₂`.
--
--   Source: https://github.com/haruhisa-enomoto/pretorsion-image-closed/blob/e803b5d1325bc1ce2b779efbff157b6cd3234bc8/PretorsionImageClosed/LinearQuiver/SummandReduction.lean#L109-L117
-- source:
--   https://github.com/haruhisa-enomoto/pretorsion-image-closed/blob/e803b5d1325bc1ce2b779efbff157b6cd3234bc8/PretorsionImageClosed/LinearQuiver/SummandReduction.lean#L109-L117

module
public import Definitions.Def_PretorsionImageClosed_LinearQuiver_Subobjects
public import Definitions.Def_PretorsionImageClosed_LinearQuiver_SummandReduction
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

theorem PretorsionImageClosed.LinearQuiver.epi_or_epi_of_epi_biprod_desc {a d : Fin n} {Y₁ Y₂ : Statement.LinRep k n}
    (f : Y₁ ⟶ interval k a d) (g : Y₂ ⟶ interval k a d) [Epi (biprod.desc f g)] : Epi f ∨ Epi g := by sorry
