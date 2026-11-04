-- Prove2me | Theorems.Thm_ThreeSum_BlockRows_mem_row
-- name    : ThreeSum.BlockRows.mem_row
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T07:17:47.689418+00:00
-- url     : https://prove2.me/theorems/cdac91be-458b-4034-87cb-b69b44bf7feb
-- title:
--   Block Rows: mem row
-- statement:
--   The Block Rows construction uses the mem row property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/BlockRows.lean#L40-L42
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/BlockRows.lean#L40-L42

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

theorem ThreeSum.BlockRows.mem_row {J L : ℕ} {S : Finset (Coord J L)} {i : Fin J} {x : Fin L} :
    x ∈ row S i ↔ Sigma.mk i x ∈ S := by sorry
