-- Prove2me | Theorems.Thm_PretorsionImageClosed_Statement_IsDelta_sum
-- name    : PretorsionImageClosed.Statement.IsDelta.sum
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-25T01:18:33.102837+00:00
-- url     : https://prove2.me/theorems/dce2dbba-2ad9-493e-bfd7-5372d1c5a437
-- title:
--   Is Delta: sum
-- statement:
--   The Is Delta construction uses the sum property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/haruhisa-enomoto/pretorsion-image-closed/blob/e803b5d1325bc1ce2b779efbff157b6cd3234bc8/PretorsionImageClosed/Gandhi/Delta.lean#L58-L65
-- source:
--   https://github.com/haruhisa-enomoto/pretorsion-image-closed/blob/e803b5d1325bc1ce2b779efbff157b6cd3234bc8/PretorsionImageClosed/Gandhi/Delta.lean#L58-L65

module
public import Definitions.Def_PretorsionImageClosed_Statement
public import Mathlib.Tactic.LinearCombination
public import Definitions.Def_PretorsionImageClosed_Gandhi_Delta
set_option autoImplicit true
@[expose] public section
public section
set_option autoImplicit false
noncomputable section
open PretorsionImageClosed PretorsionImageClosed.Statement
open Polynomial

theorem PretorsionImageClosed.Statement.IsDelta.sum {ι : Type*} (s : Finset ι) (f g : ι → Rq[X])
    (h : ∀ i ∈ s, IsDelta (f i) (g i)) : IsDelta (∑ i ∈ s, f i) (∑ i ∈ s, g i) := by sorry
