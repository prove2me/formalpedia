-- Prove2me | Theorems.Thm_ThreeSum_BlockRows_mem_prefixIndices
-- name    : ThreeSum.BlockRows.mem_prefixIndices
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T07:18:03.795385+00:00
-- url     : https://prove2.me/theorems/f27fc161-a944-4a7d-be0a-6856d4f51107
-- title:
--   Block Rows: mem prefix Indices
-- statement:
--   The Block Rows construction uses the mem prefix Indices property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/BlockRows.lean#L116-L117
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/BlockRows.lean#L116-L117

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

theorem ThreeSum.BlockRows.mem_prefixIndices {J k : ℕ} {i : Fin J} :
    i ∈ prefixIndices J k ↔ i.val < k := by sorry
