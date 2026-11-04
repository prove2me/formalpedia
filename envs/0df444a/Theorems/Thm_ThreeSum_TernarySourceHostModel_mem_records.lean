-- Prove2me | Theorems.Thm_ThreeSum_TernarySourceHostModel_mem_records
-- name    : ThreeSum.TernarySourceHostModel.mem_records
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T10:22:20.939916+00:00
-- url     : https://prove2.me/theorems/66988885-e6b2-416c-80c3-dfdf9ed60d8d
-- title:
--   Ternary Source Host Model: mem records
-- statement:
--   The Ternary Source Host Model construction uses the mem records property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/TernarySourceHostModel.lean#L15-L19
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/TernarySourceHostModel.lean#L15-L19

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

theorem ThreeSum.TernarySourceHostModel.mem_records (M NL NR : ℕ) (input dictionary : ℕ → ℤ) (pair : ℕ × ℕ) :
    pair∈records M NL NR input dictionary ↔ pair.1<NL ∧ pair.2<NR ∧
      (M : ℤ)∣input pair.1-dictionary pair.2 := by sorry
