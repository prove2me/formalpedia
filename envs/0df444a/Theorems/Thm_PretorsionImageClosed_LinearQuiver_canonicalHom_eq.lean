-- Prove2me | Theorems.Thm_PretorsionImageClosed_LinearQuiver_canonicalHom_eq
-- name    : PretorsionImageClosed.LinearQuiver.canonicalHom_eq
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-25T01:25:31.027793+00:00
-- url     : https://prove2.me/theorems/8dc486b4-421d-455e-b956-7649751728de
-- title:
--   Linear Quiver: canonical Hom eq
-- statement:
--   `canonicalHom = intervalProj ≫ intervalIncl`.
--
--   Source: https://github.com/haruhisa-enomoto/pretorsion-image-closed/blob/e803b5d1325bc1ce2b779efbff157b6cd3234bc8/PretorsionImageClosed/LinearQuiver/Hom.lean#L226-L243
-- source:
--   https://github.com/haruhisa-enomoto/pretorsion-image-closed/blob/e803b5d1325bc1ce2b779efbff157b6cd3234bc8/PretorsionImageClosed/LinearQuiver/Hom.lean#L226-L243

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

theorem PretorsionImageClosed.LinearQuiver.canonicalHom_eq {c d a b : Fin n} (hac : a ≤ c) (hbd : b ≤ d) :
    canonicalHom (k := k) hac hbd = intervalProj k c hbd ≫ intervalIncl k b hac := by sorry
