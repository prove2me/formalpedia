-- Prove2me | Theorems.Thm_ThreeSum_SubsetAddress_throughWork_bound
-- name    : ThreeSum.SubsetAddress.throughWork_bound
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T06:38:14.780342+00:00
-- url     : https://prove2.me/theorems/b07a24bb-09b8-47ee-8306-d3c71b838c61
-- title:
--   Subset Address: through Work bound
-- statement:
--   The Subset Address construction uses the through Work bound property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/SubsetAddress.lean#L361-L369
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/SubsetAddress.lean#L361-L369

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

theorem ThreeSum.SubsetAddress.throughWork_bound (L k : ℕ) :
    throughWork L k ≤ (4 * L + k + 1) * layerOffset L (k + 1) + 2 * k + 1 := by sorry
