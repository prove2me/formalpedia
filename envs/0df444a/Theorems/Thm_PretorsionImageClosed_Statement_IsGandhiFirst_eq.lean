-- Prove2me | Theorems.Thm_PretorsionImageClosed_Statement_IsGandhiFirst_eq
-- name    : PretorsionImageClosed.Statement.IsGandhiFirst.eq
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-25T02:10:05.079286+00:00
-- url     : https://prove2.me/theorems/294467b8-2276-47f2-9264-670dde9b9166
-- title:
--   Is Gandhi First: eq
-- statement:
--   The Is Gandhi First construction uses the eq property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/haruhisa-enomoto/pretorsion-image-closed/blob/e803b5d1325bc1ce2b779efbff157b6cd3234bc8/PretorsionImageClosed/Gandhi/Delta.lean#L161-L176
-- source:
--   https://github.com/haruhisa-enomoto/pretorsion-image-closed/blob/e803b5d1325bc1ce2b779efbff157b6cd3234bc8/PretorsionImageClosed/Gandhi/Delta.lean#L161-L176

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

theorem PretorsionImageClosed.Statement.IsGandhiFirst.eq {B B' : ℕ → Rq[X]} (hB : IsGandhiFirst B) (hB' : IsGandhiFirst B') :
    ∀ m, 1 ≤ m → B m = B' m := by sorry
