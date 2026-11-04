-- Prove2me | Theorems.Thm_ThreeSum_TernaryBank_rank_mono
-- name    : ThreeSum.TernaryBank.rank_mono
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T06:33:37.870609+00:00
-- url     : https://prove2.me/theorems/b126111b-a8a8-49e0-8a25-dab8a486efa0
-- title:
--   Ternary Bank: rank mono
-- statement:
--   The Ternary Bank construction uses the rank mono property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/TernaryBank.lean#L47-L48
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/TernaryBank.lean#L47-L48

import Definitions.Def_Submission_ThreeSum_TernaryJointType
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Definitions.Def_Submission_ThreeSum_TernaryBank
set_option autoImplicit false
noncomputable section
open ThreeSum ThreeSum.TernaryBank
open Finset
open ThreeSum.TernaryJointType

theorem ThreeSum.TernaryBank.rank_mono {N : ℕ} {R Q : TritWord N} (h : Below R Q) : rank R ≤ rank Q := by sorry
