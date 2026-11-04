-- Prove2me | Theorems.Thm_ThreeSum_SubsetAddress_downsetEnumerationWork_bound
-- name    : ThreeSum.SubsetAddress.downsetEnumerationWork_bound
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T06:38:16.494192+00:00
-- url     : https://prove2.me/theorems/f1106ffc-9357-4f01-9dca-ddb24369a288
-- title:
--   Subset Address: downset Enumeration Work bound
-- statement:
--   The Subset Address construction uses the downset Enumeration Work bound property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/SubsetAddress.lean#L373-L378
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/SubsetAddress.lean#L373-L378

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

theorem ThreeSum.SubsetAddress.downsetEnumerationWork_bound (L cut : ℕ) :
    downsetEnumerationWork L cut ≤ (5 * L + 1) * downsetCap L cut + 2 * L + 1 := by sorry
