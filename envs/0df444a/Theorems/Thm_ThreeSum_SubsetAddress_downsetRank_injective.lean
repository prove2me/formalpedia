-- Prove2me | Theorems.Thm_ThreeSum_SubsetAddress_downsetRank_injective
-- name    : ThreeSum.SubsetAddress.downsetRank_injective
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T06:36:39.066356+00:00
-- url     : https://prove2.me/theorems/4e816aac-647f-4818-83dc-3f514634f755
-- title:
--   Subset Address: downset Rank injective
-- statement:
--   The Subset Address construction uses the downset Rank injective property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/SubsetAddress.lean#L292-L303
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/SubsetAddress.lean#L292-L303

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

theorem ThreeSum.SubsetAddress.downsetRank_injective {L m n : ℕ} (hm : m < 2 ^ L) (hn : n < 2 ^ L)
    (he : downsetRank L m = downsetRank L n) : m = n := by sorry
