-- Prove2me | Theorems.Thm_PretorsionImageClosed_Statement_IsDelta_unique
-- name    : PretorsionImageClosed.Statement.IsDelta.unique
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-25T01:07:33.42579+00:00
-- url     : https://prove2.me/theorems/af962af3-6181-48a8-8660-65687b2efced
-- title:
--   Is Delta: unique
-- statement:
--   The Is Delta construction uses the unique property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/haruhisa-enomoto/pretorsion-image-closed/blob/e803b5d1325bc1ce2b779efbff157b6cd3234bc8/PretorsionImageClosed/Gandhi/Delta.lean#L72-L75
-- source:
--   https://github.com/haruhisa-enomoto/pretorsion-image-closed/blob/e803b5d1325bc1ce2b779efbff157b6cd3234bc8/PretorsionImageClosed/Gandhi/Delta.lean#L72-L75

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

theorem PretorsionImageClosed.Statement.IsDelta.unique {f g g' : Rq[X]} (h : IsDelta f g) (h' : IsDelta f g') : g = g' := by sorry
