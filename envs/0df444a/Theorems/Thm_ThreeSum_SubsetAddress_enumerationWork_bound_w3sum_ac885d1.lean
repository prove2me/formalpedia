-- Prove2me | Theorems.Thm_ThreeSum_SubsetAddress_enumerationWork_bound_w3sum_ac885d1
-- name    : ThreeSum.SubsetAddress.enumerationWork_bound_w3sum_ac885d1
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T07:02:09.13602+00:00
-- url     : https://prove2.me/theorems/3b02e9f3-50e1-4278-89bb-d478441de0af
-- title:
--   Subset Address: enumeration Work bound
-- statement:
--   The Subset Address construction uses the enumeration Work bound property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/SubsetAddress.lean#L234-L250
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/SubsetAddress.lean#L234-L250

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

theorem ThreeSum.SubsetAddress.enumerationWork_bound_w3sum_ac885d1 (L k : ℕ) :
    enumerationWork L k ≤ (4 * L + 1) * L.choose k + 1 := by sorry
