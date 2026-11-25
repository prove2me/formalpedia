-- Prove2me | Theorems.Thm_PretorsionImageClosed_SetClosure_exists_finite_isMinimalGenerator
-- name    : PretorsionImageClosed.SetClosure.exists_finite_isMinimalGenerator
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-25T06:17:46.397875+00:00
-- url     : https://prove2.me/theorems/a2749c92-79f7-5f9f-bc9b-0c2720bfe101
-- title:
--   Set Closure: exists finite is Minimal Generator
-- statement:
--   A finite generating set contains an inclusion-minimal finite
--   generating subset, without assuming that the entire ground type is finite.
--
--   Source: https://github.com/haruhisa-enomoto/pretorsion-image-closed/blob/e803b5d1325bc1ce2b779efbff157b6cd3234bc8/PretorsionImageClosed/ConvexGeometry/Compact.lean#L218-L239
-- source:
--   https://github.com/haruhisa-enomoto/pretorsion-image-closed/blob/e803b5d1325bc1ce2b779efbff157b6cd3234bc8/PretorsionImageClosed/ConvexGeometry/Compact.lean#L218-L239

module
public import Mathlib.Order.CompactlyGenerated.Basic
public import Definitions.Def_PretorsionImageClosed_ConvexGeometry_CompletelyJoinIrreducible
public import Definitions.Def_PretorsionImageClosed_ConvexGeometry_Compact
set_option autoImplicit true
@[expose] public section
public section
open Set
open PretorsionImageClosed PretorsionImageClosed.SetClosure
variable {E : Type*} {c : SetClosure E}

theorem PretorsionImageClosed.SetClosure.exists_finite_isMinimalGenerator
    {B C : Set E} (hBfin : B.Finite) (hBC : c B = C) :
    ∃ B₀ : Set E, B₀.Finite ∧ B₀ ⊆ B ∧ c.IsMinimalGenerator B₀ C := by sorry
