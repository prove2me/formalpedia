-- Prove2me | Theorems.Thm_ThreeSum_TernarySourceHostModel_sum_getD
-- name    : ThreeSum.TernarySourceHostModel.sum_getD
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T10:22:35.660615+00:00
-- url     : https://prove2.me/theorems/305ad39c-bfe5-46ea-927d-552732b67d2c
-- title:
--   Ternary Source Host Model: sum get D
-- statement:
--   The Ternary Source Host Model construction uses the sum get D property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/TernarySourceHostModel.lean#L29-L42
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/TernarySourceHostModel.lean#L29-L42

import Definitions.Def_Submission_ThreeSum_LightTernarySourceHost
import Definitions.Def_Submission_ThreeSum_TernaryWeightedPhysicalSources
import Definitions.Def_Submission_ThreeSum_TernaryCodeSemantics
import Definitions.Def_Submission_ThreeSum_TernarySourceHostModel
set_option autoImplicit false
noncomputable section
open ThreeSum ThreeSum.TernarySourceHostModel
open Finset Light TernaryJointType
open scoped BigOperators
variable {N : ℕ}

theorem ThreeSum.TernarySourceHostModel.sum_getD {A : Type*} [DecidableEq A] (ps : List A) (fallback : A)
    (hn : ps.Nodup) (f : A → ℤ) :
    (∑ i∈range ps.length, f (ps.getD i fallback))=∑ pair∈ps.toFinset, f pair := by sorry
