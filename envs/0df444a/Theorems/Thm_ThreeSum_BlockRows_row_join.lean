-- Prove2me | Theorems.Thm_ThreeSum_BlockRows_row_join
-- name    : ThreeSum.BlockRows.row_join
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T07:17:48.974752+00:00
-- url     : https://prove2.me/theorems/b86019d5-1174-4edc-9e6b-c3c1df4ab0d5
-- title:
--   Block Rows: row join
-- statement:
--   The Block Rows construction uses the row join property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/BlockRows.lean#L50-L54
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/BlockRows.lean#L50-L54

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

theorem ThreeSum.BlockRows.row_join {J L : ℕ} (I : Finset (Fin J))
    (u : Fin J → Finset (Fin L)) (i : Fin J) :
    row (join I u) i = if i ∈ I then u i else ∅ := by sorry
