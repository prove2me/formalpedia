-- Prove2me | Theorems.Thm_PretorsionImageClosed_SetClosure_isCompactElement_iff_exists_finite_generator
-- name    : PretorsionImageClosed.SetClosure.isCompactElement_iff_exists_finite_generator
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-25T06:30:13.383902+00:00
-- url     : https://prove2.me/theorems/e874a028-9ce5-4d2c-ade5-559242d786b1
-- title:
--   Set Closure: is Compact Element iff exists finite generator
-- statement:
--   For a finitary closure operator, compact closed sets are exactly the
--   closures of finite subsets.  The generator can always be chosen inside
--   the closed set.
--
--   Source: https://github.com/haruhisa-enomoto/pretorsion-image-closed/blob/e803b5d1325bc1ce2b779efbff157b6cd3234bc8/PretorsionImageClosed/ConvexGeometry/Compact.lean#L201-L213
-- source:
--   https://github.com/haruhisa-enomoto/pretorsion-image-closed/blob/e803b5d1325bc1ce2b779efbff157b6cd3234bc8/PretorsionImageClosed/ConvexGeometry/Compact.lean#L201-L213

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

theorem PretorsionImageClosed.SetClosure.isCompactElement_iff_exists_finite_generator
    (hfin : c.IsFinitary) {C : c.Closeds} :
    IsCompactElement C ↔
      ∃ B : Set E, B.Finite ∧ B ⊆ (C : Set E) ∧
        c B = (C : Set E) := by sorry
