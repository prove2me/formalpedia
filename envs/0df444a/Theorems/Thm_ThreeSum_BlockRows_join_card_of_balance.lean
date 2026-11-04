-- Prove2me | Theorems.Thm_ThreeSum_BlockRows_join_card_of_balance
-- name    : ThreeSum.BlockRows.join_card_of_balance
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T07:17:57.092474+00:00
-- url     : https://prove2.me/theorems/8b46b1c9-a389-4d85-814d-fbbdbc389ba8
-- title:
--   Block Rows: join card of balance
-- statement:
--   The Block Rows construction uses the join card of balance property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/BlockRows.lean#L98-L102
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/BlockRows.lean#L98-L102

import Mathlib.Data.Finset.Sigma
import Mathlib.Algebra.BigOperators.Group.Finset.Sigma
import Mathlib.Data.Fintype.Card
import Mathlib.Tactic.Tauto
import Mathlib.Algebra.Ring.Nat
import Lean.Elab.Tactic.Omega
import Mathlib.Tactic.Ring
import Definitions.Def_Submission_ThreeSum_BlockRows
set_option autoImplicit false
open ThreeSum ThreeSum.BlockRows
open Finset
open scoped BigOperators

theorem ThreeSum.BlockRows.join_card_of_balance {J L h : ℕ} (I : Finset (Fin J))
    (u : Fin J → Finset (Fin L)) (hu : ∀ i ∈ I, (u i).card = h) :
    (join I u).card = I.card * h := by sorry
