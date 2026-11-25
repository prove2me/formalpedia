-- Prove2me | Theorems.Thm_PretorsionImageClosed_LinearQuiver_mono_or_mono_of_mono_biprod_lift
-- name    : PretorsionImageClosed.LinearQuiver.mono_or_mono_of_mono_biprod_lift
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-25T03:13:25.637561+00:00
-- url     : https://prove2.me/theorems/c6d96b36-b48a-56fe-a07e-beca73cf7667
-- title:
--   Linear Quiver: mono or mono of mono biprod lift
-- statement:
--   Lemma 5.3(2): if `M_{a,d}` is a subobject of `Y₁ ⊞ Y₂`, it is a subobject of `Y₁`
--   or of `Y₂`.
--
--   Source: https://github.com/haruhisa-enomoto/pretorsion-image-closed/blob/e803b5d1325bc1ce2b779efbff157b6cd3234bc8/PretorsionImageClosed/LinearQuiver/SummandReduction.lean#L121-L130
-- source:
--   https://github.com/haruhisa-enomoto/pretorsion-image-closed/blob/e803b5d1325bc1ce2b779efbff157b6cd3234bc8/PretorsionImageClosed/LinearQuiver/SummandReduction.lean#L121-L130

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

theorem PretorsionImageClosed.LinearQuiver.mono_or_mono_of_mono_biprod_lift {a d : Fin n} {Y₁ Y₂ : Statement.LinRep k n}
    (f : interval k a d ⟶ Y₁) (g : interval k a d ⟶ Y₂) [Mono (biprod.lift f g)] :
    Mono f ∨ Mono g := by sorry
