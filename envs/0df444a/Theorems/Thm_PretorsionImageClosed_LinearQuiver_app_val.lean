-- Prove2me | Theorems.Thm_PretorsionImageClosed_LinearQuiver_app_val
-- name    : PretorsionImageClosed.LinearQuiver.app_val
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-25T01:20:30.041078+00:00
-- url     : https://prove2.me/theorems/2e03f61d-930a-4be5-80a2-2aac391bb76d
-- title:
--   Linear Quiver: app val
-- statement:
--   The value of `η` on an arbitrary vector.
--
--   Source: https://github.com/haruhisa-enomoto/pretorsion-image-closed/blob/e803b5d1325bc1ce2b779efbff157b6cd3234bc8/PretorsionImageClosed/LinearQuiver/Hom.lean#L76-L82
-- source:
--   https://github.com/haruhisa-enomoto/pretorsion-image-closed/blob/e803b5d1325bc1ce2b779efbff157b6cd3234bc8/PretorsionImageClosed/LinearQuiver/Hom.lean#L76-L82

module
public import Definitions.Def_PretorsionImageClosed_LinearQuiver_Interval
public import Definitions.Def_PretorsionImageClosed_Subobjects_Preimage
public import Definitions.Def_PretorsionImageClosed_Length_Representations
public import Mathlib.CategoryTheory.Limits.FunctorCategory.EpiMono
public import Definitions.Def_PretorsionImageClosed_LinearQuiver_Hom
set_option autoImplicit true
@[expose] public section
public section
set_option autoImplicit false
noncomputable section
open PretorsionImageClosed
open CategoryTheory Limits
open PretorsionImageClosed.LinearQuiver
universe u
variable (k : Type u) [Field k] {n : ℕ}
variable {k}

theorem PretorsionImageClosed.LinearQuiver.app_val {c d a b : Fin n} (η : interval k c d ⟶ interval k a b) (i : Fin n)
    (x : intervalSpace k c d i) :
    ((η.app i).hom.hom x).1 = (x : k) * coord η i := by sorry
