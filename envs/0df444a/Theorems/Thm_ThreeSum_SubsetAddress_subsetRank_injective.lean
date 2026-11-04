-- Prove2me | Theorems.Thm_ThreeSum_SubsetAddress_subsetRank_injective
-- name    : ThreeSum.SubsetAddress.subsetRank_injective
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T06:38:24.187879+00:00
-- url     : https://prove2.me/theorems/bb69d950-3b96-4933-ad5f-bbda8f35019f
-- title:
--   Subset Address: subset Rank injective
-- statement:
--   The Subset Address construction uses the subset Rank injective property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/SubsetAddress.lean#L441-L444
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/SubsetAddress.lean#L441-L444

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

theorem ThreeSum.SubsetAddress.subsetRank_injective (L : ℕ) : Function.Injective (@subsetRank L) := by sorry
