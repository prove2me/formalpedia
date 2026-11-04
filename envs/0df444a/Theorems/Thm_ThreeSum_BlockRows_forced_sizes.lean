-- Prove2me | Theorems.Thm_ThreeSum_BlockRows_forced_sizes
-- name    : ThreeSum.BlockRows.forced_sizes
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T07:18:05.804144+00:00
-- url     : https://prove2.me/theorems/12790bee-ed08-46ad-bc1b-4dbf878f7582
-- title:
--   Block Rows: forced sizes
-- statement:
--   Size arithmetic for the actual remaining Q blocks. The parameter I is
--   any set of completed blocks, including the initial segment used in reporting.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/BlockRows.lean#L121-L135
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/BlockRows.lean#L121-L135

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

theorem ThreeSum.BlockRows.forced_sizes {J L h : ℕ} (I : Finset (Fin J))
    (Q u : Fin J → Finset (Fin L)) (hQ : ∀ i, (Q i).card = 2 * h)
    (hu : ∀ i ∈ I, u i ⊆ Q i ∧ (u i).card = h) :
    (join Iᶜ Q).card =
      (J * h - (join I u).card) +
      (J * h - (join I (fun i => Q i \ u i)).card) := by sorry
