-- Prove2me | Theorems.Thm_ThreeSum_BlockRows_join_subset
-- name    : ThreeSum.BlockRows.join_subset
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T07:17:55.628952+00:00
-- url     : https://prove2.me/theorems/ab474350-ae10-4f49-a312-428dc6ba90e3
-- title:
--   Block Rows: join subset
-- statement:
--   The Block Rows construction uses the join subset property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/BlockRows.lean#L89-L93
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/BlockRows.lean#L89-L93

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

theorem ThreeSum.BlockRows.join_subset {J L : ℕ} (I : Finset (Fin J)) {u v : Fin J → Finset (Fin L)}
    (h : ∀ i ∈ I, u i ⊆ v i) : join I u ⊆ join I v := by sorry
