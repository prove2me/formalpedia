-- Prove2me | Theorems.Thm_PretorsionImageClosed_Statement_isTorsionPair_iff
-- name    : PretorsionImageClosed.Statement.isTorsionPair_iff
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-25T06:48:54.705389+00:00
-- url     : https://prove2.me/theorems/6e651152-1961-4da7-9178-52b42c6de9f7
-- title:
--   Statement: is Torsion Pair iff
-- statement:
--   **Proposition 2.5.** `(T, F)` is a torsion pair iff it is a pretorsion theory with
--   `T ∩ F = 0`.
--
--   Source: https://github.com/haruhisa-enomoto/pretorsion-image-closed/blob/e803b5d1325bc1ce2b779efbff157b6cd3234bc8/PretorsionImageClosed/Pretorsion/TorsionPairs.lean#L52-L86
-- source:
--   https://github.com/haruhisa-enomoto/pretorsion-image-closed/blob/e803b5d1325bc1ce2b779efbff157b6cd3234bc8/PretorsionImageClosed/Pretorsion/TorsionPairs.lean#L52-L86

module
public import Definitions.Def_PretorsionImageClosed_Pretorsion_FixedMiddle
public import Mathlib.Algebra.Homology.ShortComplex.ShortExact
public import Definitions.Def_PretorsionImageClosed_Pretorsion_TorsionPairs
set_option autoImplicit true
@[expose] public section
public section
set_option autoImplicit false
noncomputable section
open PretorsionImageClosed PretorsionImageClosed.Statement
open CategoryTheory Limits Subcategory ZeroObject
variable {C : Type*} [Category C] [Abelian C]

theorem PretorsionImageClosed.Statement.isTorsionPair_iff (T F : Subcategory C) :
    IsTorsionPair T.prop F.prop ↔
      IsPretorsionTheory T.prop F.prop ∧ ∀ X, (T.prop ⊓ F.prop) X → IsZero X := by sorry
