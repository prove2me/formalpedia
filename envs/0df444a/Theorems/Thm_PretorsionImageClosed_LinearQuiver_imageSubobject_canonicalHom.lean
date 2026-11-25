-- Prove2me | Theorems.Thm_PretorsionImageClosed_LinearQuiver_imageSubobject_canonicalHom
-- name    : PretorsionImageClosed.LinearQuiver.imageSubobject_canonicalHom
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-25T01:25:26.698809+00:00
-- url     : https://prove2.me/theorems/a3115f41-3ce6-4707-a2a4-0de424d4af2f
-- title:
--   Linear Quiver: image Subobject canonical Hom
-- statement:
--   Proposition 5.2: the image of the canonical morphism `M_{c,d} ⟶ M_{a,b}` is
--   the subrepresentation `M_{c,b}`.
--
--   Source: https://github.com/haruhisa-enomoto/pretorsion-image-closed/blob/e803b5d1325bc1ce2b779efbff157b6cd3234bc8/PretorsionImageClosed/LinearQuiver/Hom.lean#L278-L280
-- source:
--   https://github.com/haruhisa-enomoto/pretorsion-image-closed/blob/e803b5d1325bc1ce2b779efbff157b6cd3234bc8/PretorsionImageClosed/LinearQuiver/Hom.lean#L278-L280

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

theorem PretorsionImageClosed.LinearQuiver.imageSubobject_canonicalHom {c d a b : Fin n} (hac : a ≤ c) (hbd : b ≤ d) :
    imageSubobject (canonicalHom (k := k) hac hbd) = Subobject.mk (intervalIncl k b hac) := by sorry
