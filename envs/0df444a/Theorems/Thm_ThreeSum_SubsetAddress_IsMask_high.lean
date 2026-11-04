-- Prove2me | Theorems.Thm_ThreeSum_SubsetAddress_IsMask_high
-- name    : ThreeSum.SubsetAddress.IsMask.high
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T06:32:49.968208+00:00
-- url     : https://prove2.me/theorems/ed5ea361-06d6-447d-bebe-00844cbaf2ee
-- title:
--   Is Mask: high
-- statement:
--   The Is Mask construction uses the high property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/SubsetAddress.lean#L86-L92
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/SubsetAddress.lean#L86-L92

import Mathlib.Data.Nat.Choose.Basic
import Mathlib.Data.List.Basic
import Mathlib.Data.List.Nodup
import Mathlib.Data.Finset.Powerset
import Mathlib.Data.Fin.Embedding
import Mathlib.Combinatorics.Colex
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import Lean.Elab.Tactic.Omega
import Definitions.Def_Submission_ThreeSum_SubsetAddress
set_option autoImplicit false
open ThreeSum ThreeSum.SubsetAddress
set_option maxRecDepth 4000
open Finset
open scoped BigOperators

theorem ThreeSum.SubsetAddress.IsMask.high {L k m : ℕ} (hm : IsMask (L + 1) k m) (hc : 2 ^ L ≤ m) :
    0 < k ∧ IsMask L (k - 1) (m - 2 ^ L) := by sorry
