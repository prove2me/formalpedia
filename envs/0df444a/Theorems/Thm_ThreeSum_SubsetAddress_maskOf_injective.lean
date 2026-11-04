-- Prove2me | Theorems.Thm_ThreeSum_SubsetAddress_maskOf_injective
-- name    : ThreeSum.SubsetAddress.maskOf_injective
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T06:38:15.151199+00:00
-- url     : https://prove2.me/theorems/9b8aeb64-e16e-4f25-b75d-8e10102e0ac0
-- title:
--   Subset Address: mask Of injective
-- statement:
--   The Subset Address construction uses the mask Of injective property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/SubsetAddress.lean#L383-L384
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/SubsetAddress.lean#L383-L384

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

theorem ThreeSum.SubsetAddress.maskOf_injective : Function.Injective maskOf := by sorry
