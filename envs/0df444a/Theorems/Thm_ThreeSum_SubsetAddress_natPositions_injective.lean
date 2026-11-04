-- Prove2me | Theorems.Thm_ThreeSum_SubsetAddress_natPositions_injective
-- name    : ThreeSum.SubsetAddress.natPositions_injective
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T06:38:20.062492+00:00
-- url     : https://prove2.me/theorems/400870a5-005f-4419-ba15-883618343d8b
-- title:
--   Subset Address: nat Positions injective
-- statement:
--   The Subset Address construction uses the nat Positions injective property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/SubsetAddress.lean#L422-L423
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/SubsetAddress.lean#L422-L423

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

theorem ThreeSum.SubsetAddress.natPositions_injective (L : ℕ) :
    Function.Injective (@natPositions L) := by sorry
