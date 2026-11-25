-- Prove2me | Theorems.Thm_PretorsionImageClosed_SetClosure_finiteClosuresBelow_directed_sSup
-- name    : PretorsionImageClosed.SetClosure.finiteClosuresBelow_directed_sSup
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-25T06:29:59.82335+00:00
-- url     : https://prove2.me/theorems/767ed0bb-3769-4c18-b2ce-68027e860afc
-- title:
--   Set Closure: finite Closures Below directed s Sup
-- statement:
--   Every closed set is the directed supremum of the closures of its
--   finite subsets.  Under finitarity, all members of this directed family
--   are compact.
--
--   Source: https://github.com/haruhisa-enomoto/pretorsion-image-closed/blob/e803b5d1325bc1ce2b779efbff157b6cd3234bc8/PretorsionImageClosed/ConvexGeometry/Compact.lean#L114-L145
-- source:
--   https://github.com/haruhisa-enomoto/pretorsion-image-closed/blob/e803b5d1325bc1ce2b779efbff157b6cd3234bc8/PretorsionImageClosed/ConvexGeometry/Compact.lean#L114-L145

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

theorem PretorsionImageClosed.SetClosure.finiteClosuresBelow_directed_sSup
    (hfin : c.IsFinitary) (C : c.Closeds) :
    (c.finiteClosuresBelow C).Nonempty ∧
      DirectedOn (· ≤ ·) (c.finiteClosuresBelow C) ∧
      (∀ K ∈ c.finiteClosuresBelow C, IsCompactElement K) ∧
      sSup (c.finiteClosuresBelow C) = C := by sorry
