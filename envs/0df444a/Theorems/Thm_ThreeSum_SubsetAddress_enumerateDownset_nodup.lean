-- Prove2me | Theorems.Thm_ThreeSum_SubsetAddress_enumerateDownset_nodup
-- name    : ThreeSum.SubsetAddress.enumerateDownset_nodup
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T06:36:43.543453+00:00
-- url     : https://prove2.me/theorems/a68b9f45-97f1-4dee-8ca1-5deed21d90eb
-- title:
--   Subset Address: enumerate Downset nodup
-- statement:
--   The Subset Address construction uses the enumerate Downset nodup property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/SubsetAddress.lean#L353-L354
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/SubsetAddress.lean#L353-L354

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

theorem ThreeSum.SubsetAddress.enumerateDownset_nodup (L cut : ℕ) : (enumerateDownset L cut).Nodup := by sorry
