-- Prove2me | Theorems.Thm_ThreeSum_SubsetAddress_enumerateThrough_nodup
-- name    : ThreeSum.SubsetAddress.enumerateThrough_nodup
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T06:36:42.793935+00:00
-- url     : https://prove2.me/theorems/5f21e579-3b33-4287-b45a-7c598a938331
-- title:
--   Subset Address: enumerate Through nodup
-- statement:
--   The Subset Address construction uses the enumerate Through nodup property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/SubsetAddress.lean#L342-L351
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/SubsetAddress.lean#L342-L351

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

theorem ThreeSum.SubsetAddress.enumerateThrough_nodup (L k : ℕ) : (enumerateThrough L k).Nodup := by sorry
