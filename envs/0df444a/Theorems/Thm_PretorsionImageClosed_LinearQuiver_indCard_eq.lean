-- Prove2me | Theorems.Thm_PretorsionImageClosed_LinearQuiver_indCard_eq
-- name    : PretorsionImageClosed.LinearQuiver.indCard_eq
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-25T03:27:25.075058+00:00
-- url     : https://prove2.me/theorems/8cd273c7-3b10-4add-9300-eabe75b003c5
-- title:
--   Linear Quiver: ind Card eq
-- statement:
--   `|ind C|` is the number of intervals of `C`.
--
--   Source: https://github.com/haruhisa-enomoto/pretorsion-image-closed/blob/e803b5d1325bc1ce2b779efbff157b6cd3234bc8/PretorsionImageClosed/LinearQuiver/Counting.lean#L80-L81
-- source:
--   https://github.com/haruhisa-enomoto/pretorsion-image-closed/blob/e803b5d1325bc1ce2b779efbff157b6cd3234bc8/PretorsionImageClosed/LinearQuiver/Counting.lean#L80-L81

module
public import Definitions.Def_PretorsionImageClosed_LinearQuiver_IntervalSets
public import Definitions.Def_PretorsionImageClosed_LinearQuiver_Counting
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
variable (C : Subcategory (Statement.LinRep k n))

theorem PretorsionImageClosed.LinearQuiver.indCard_eq : indCard C.prop = Nat.card (IntervalPairs C) := by sorry
