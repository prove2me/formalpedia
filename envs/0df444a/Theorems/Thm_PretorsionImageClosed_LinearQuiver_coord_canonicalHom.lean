-- Prove2me | Theorems.Thm_PretorsionImageClosed_LinearQuiver_coord_canonicalHom
-- name    : PretorsionImageClosed.LinearQuiver.coord_canonicalHom
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-25T01:21:11.429623+00:00
-- url     : https://prove2.me/theorems/32d9fd93-5daf-4487-ba36-53ec6256643f
-- title:
--   Linear Quiver: coord canonical Hom
-- statement:
--   The Linear Quiver construction uses the coord canonical Hom property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/haruhisa-enomoto/pretorsion-image-closed/blob/e803b5d1325bc1ce2b779efbff157b6cd3234bc8/PretorsionImageClosed/LinearQuiver/Hom.lean#L199-L209
-- source:
--   https://github.com/haruhisa-enomoto/pretorsion-image-closed/blob/e803b5d1325bc1ce2b779efbff157b6cd3234bc8/PretorsionImageClosed/LinearQuiver/Hom.lean#L199-L209

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

theorem PretorsionImageClosed.LinearQuiver.coord_canonicalHom {c d a b : Fin n} (hac : a ≤ c) (hbd : b ≤ d) (i : Fin n) :
    coord (canonicalHom (k := k) hac hbd) i = if c ≤ i ∧ i ≤ b then 1 else 0 := by sorry
