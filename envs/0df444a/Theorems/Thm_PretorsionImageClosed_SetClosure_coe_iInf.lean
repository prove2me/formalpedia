-- Prove2me | Theorems.Thm_PretorsionImageClosed_SetClosure_coe_iInf
-- name    : PretorsionImageClosed.SetClosure.coe_iInf
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-25T05:51:31.076114+00:00
-- url     : https://prove2.me/theorems/c5945dab-01c5-4539-a8fa-b85e358f414e
-- title:
--   Set Closure: coe i Inf
-- statement:
--   The Set Closure construction uses the coe i Inf property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/haruhisa-enomoto/pretorsion-image-closed/blob/e803b5d1325bc1ce2b779efbff157b6cd3234bc8/PretorsionImageClosed/ConvexGeometry/ClosedSets.lean#L67-L69
-- source:
--   https://github.com/haruhisa-enomoto/pretorsion-image-closed/blob/e803b5d1325bc1ce2b779efbff157b6cd3234bc8/PretorsionImageClosed/ConvexGeometry/ClosedSets.lean#L67-L69

module
public import Mathlib.Order.Grade
public import Definitions.Def_PretorsionImageClosed_ConvexGeometry_Finite
public import Definitions.Def_PretorsionImageClosed_ConvexGeometry_ClosedSets
set_option autoImplicit true
@[expose] public section
public section
open Set
open PretorsionImageClosed PretorsionImageClosed.SetClosure
variable {E : Type*}
variable {c : SetClosure E}

theorem PretorsionImageClosed.SetClosure.coe_iInf {ι : Sort*} (f : ι → c.Closeds) :
    ((⨅ i, f i : c.Closeds) : Set E) = ⋂ i, (f i : Set E) := by sorry
