-- Prove2me | Theorems.Thm_ThreeSum_TernarySourceHostModel_packed_eq_iff
-- name    : ThreeSum.TernarySourceHostModel.packed_eq_iff
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T10:22:55.99812+00:00
-- url     : https://prove2.me/theorems/aa92aa75-9efd-4fb6-8d46-0d0da0e3f40a
-- title:
--   Ternary Source Host Model: packed eq iff
-- statement:
--   The Ternary Source Host Model construction uses the packed eq iff property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/TernarySourceHostModel.lean#L44-L55
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/TernarySourceHostModel.lean#L44-L55

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

theorem ThreeSum.TernarySourceHostModel.packed_eq_iff (bank g h a b : ℕ) (ha : a<bank) (hb : b<bank) :
    g*bank+a=h*bank+b ↔ g=h ∧ a=b := by sorry
