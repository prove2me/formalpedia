-- Prove2me | Theorems.Thm_WeightedCache3SUMRefinement_e1ae71d_ThreeSum_LightWeightedGlobalPrefixSetup_allocateTime_le_bank_work
-- name    : WeightedCache3SUMRefinement_e1ae71d.ThreeSum.LightWeightedGlobalPrefixSetup.allocateTime_le_bank_work
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-04T11:06:26.204867+00:00
-- url     : https://prove2.me/theorems/1ef09c6b-316b-4dbc-9bc1-1996fb73c6f8
-- title:
--   allocateTime_le_bank_work
-- statement:
--   Refined weighted-cache 3SUM lemma. Its formal statement preserves the complete source hypotheses and conclusion.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/e1ae71db2231f172c6541820e2ce0a54aa14fc64/Submission/Weighted/Global/LightTernaryPrefixSetup.lean#L285-L290
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/e1ae71db2231f172c6541820e2ce0a54aa14fc64/Submission/Weighted/Global/LightTernaryPrefixSetup.lean#L285-L290

import Definitions.Def_WeightedCache3SUMRefinement_e1ae71d_Submission_Weighted_GlobalBank
import Definitions.Def_WeightedCache3SUMRefinement_e1ae71d_Submission_Weighted_EnumerationSetup
import Definitions.Def_Submission_ThreeSum_LightNatPower
import Definitions.Def_WeightedCache3SUMRefinement_e1ae71d_Submission_Weighted_BankCanonical
import Definitions.Def_WeightedCache3SUMRefinement_e1ae71d_Submission_Weighted_Global_DimensionBounds
import Definitions.Def_WeightedCache3SUMRefinement_e1ae71d_Submission_Weighted_Global_LightTernaryPrefixSetup
set_option autoImplicit false
open WeightedCache3SUMRefinement_e1ae71d
open _root_.ThreeSum
open WeightedCache3SUMRefinement_e1ae71d.ThreeSum WeightedCache3SUMRefinement_e1ae71d.ThreeSum.LightWeightedGlobalPrefixSetup
open Light LightSubsetAddress WeightedAddresses WeightedBankEnumeration
open WeightedGlobalLocalParameters WeightedGlobalDimensionBounds
set_option maxHeartbeats 6000000
set_option maxRecDepth 18000
variable {lim : Limits} {P : Program}

theorem WeightedCache3SUMRefinement_e1ae71d.ThreeSum.LightWeightedGlobalPrefixSetup.allocateTime_le_bank_work {m : ℕ} (hm : 0<m) (j : ℕ) :
    allocateTime m j≤2000*(N m j+1)*(nb m j+1) := by sorry
