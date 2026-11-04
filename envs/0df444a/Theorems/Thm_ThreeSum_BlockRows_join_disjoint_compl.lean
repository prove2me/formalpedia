-- Prove2me | Theorems.Thm_ThreeSum_BlockRows_join_disjoint_compl
-- name    : ThreeSum.BlockRows.join_disjoint_compl
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T07:17:56.615503+00:00
-- url     : https://prove2.me/theorems/55305aae-8c0d-4c6a-b12f-95f6adc7ad37
-- title:
--   Block Rows: join disjoint compl
-- statement:
--   The Block Rows construction uses the join disjoint compl property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/BlockRows.lean#L83-L87
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/BlockRows.lean#L83-L87

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

theorem ThreeSum.BlockRows.join_disjoint_compl {J L : ℕ} (I : Finset (Fin J))
    (u v : Fin J → Finset (Fin L)) : Disjoint (join I u) (join Iᶜ v) := by sorry
