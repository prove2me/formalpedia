-- Prove2me | Theorems.Thm_ThreeSum_LightTernaryWantedQuery_assembled_product_eq
-- name    : ThreeSum.LightTernaryWantedQuery.assembled_product_eq
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T12:21:58.593995+00:00
-- url     : https://prove2.me/theorems/78616871-0857-4570-a769-00e73d336e53
-- title:
--   Light Ternary Wanted Query: assembled product eq
-- statement:
--   The assembler's product is the full transformed product consumed by both
--   near reconstruction and the frozen query.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/LightTernaryWantedQuery.lean#L125-L128
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/LightTernaryWantedQuery.lean#L125-L128

import Definitions.Def_Submission_ThreeSum_LightTernaryNearPair
import Definitions.Def_Submission_ThreeSum_LightTernaryFrozenQueryPhysical
import Definitions.Def_Submission_ThreeSum_LightTernaryBankAssembly
import Definitions.Def_Submission_ThreeSum_LightTernaryWantedQuery
set_option autoImplicit false
noncomputable section
open ThreeSum ThreeSum.LightTernaryWantedQuery
open Light ThreeSum.LightSubsetAddress ThreeSum.TernaryJointType ThreeSum.TernaryBank
open ThreeSum.TernaryCodeSemantics ThreeSum.TernaryFrozenQueryStages ThreeSum.TernaryBankStageModel
open ThreeSum.LightTernaryNearPair
set_option maxHeartbeats 6000000
set_option maxRecDepth 12000
variable {lim : Limits} {P : Program}

theorem ThreeSum.LightTernaryWantedQuery.assembled_product_eq {N : ℕ} (F G : TritWord N→ℤ) :
    LightTernaryBankAssembly.product F G=H F G := by sorry
