-- Prove2me | Theorems.Thm_ThreeSum_WeightedGlobalCountFrontendBudget_physical_prefix_bound
-- name    : ThreeSum.WeightedGlobalCountFrontendBudget.physical_prefix_bound
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T13:19:01.978436+00:00
-- url     : https://prove2.me/theorems/378490bf-fa37-4266-b3ef-4ee06adedcc6
-- title:
--   Weighted Global Count Frontend Budget: physical prefix bound
-- statement:
--   The literal repeated family/carry/raw-cap factor is inserted into the
--   actual frontend natural time. This includes the larger field's p/Rbar volume.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/Weighted/Global/CountFrontendBudget.lean#L226-L302
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/Weighted/Global/CountFrontendBudget.lean#L226-L302

import Definitions.Def_Submission_Weighted_PreparedBudget
import Definitions.Def_Submission_Weighted_GlobalBank
import Definitions.Def_Submission_Weighted_CountFrontend
import Definitions.Def_Submission_Weighted_Global_TernaryOversizeDimensions
import Definitions.Def_Submission_Weighted_Global_CountFrontendBudget
set_option autoImplicit false
noncomputable section
open ThreeSum ThreeSum.WeightedGlobalCountFrontendBudget
open Filter Real Asymptotics
open TernaryJointType WeightedGlobalBank WeightedGlobalParameters WeightedGlobalDimensionBounds
open WeightedGlobalEntropyRates WeightedGlobalLocalParameters WeightedGlobalCoverScale WeightedGlobalOversizePrime WeightedGlobalOversizeRates
open WeightedGlobalCoverCapParameters
open WeightedGlobalOversizeOverhead WeightedGlobalOversizeDimensions WeightedGlobalPrincipalDimensions
open LightWeightedNearPair
open scoped Topology
set_option maxHeartbeats 5000000
set_option maxRecDepth 16000

theorem ThreeSum.WeightedGlobalCountFrontendBudget.physical_prefix_bound {K k m n j groups count b : ℕ}
    (hK : 0<K) (hk : 0<k) (hm : 0<m) (hn : 1<n) (hj : j≤radixLength m n)
    (c d : ℕ) (hb : b≤c*(fixedLength m+1)^d)
    (f g : Config) (hT : f.T=bankCut m j)
    (hgroups : groups≤(b*(nativeFamily K m k).length*
      WeightedGlobalCoverCapParameters.rawThreshold (nativePrime K m) (sourceCap m (nativePrime K m)) k)^j)
    (hcount : (count : ℝ)≤(n : ℝ)*((nativePrime K m : ℝ)/partitionCap m)^j*
      ((b*(nativeFamily K m k).length*
        WeightedGlobalCoverCapParameters.rawThreshold (nativePrime K m) (sourceCap m (nativePrime K m)) k : ℕ) : ℝ)^j) :
    (LightWeightedCountFrontend.time groups (fixedLength (j*m)) f.L (bankSize m j) count (queryMax m j f g)+1000 : ℕ)≤
      dimensionConstant K k c d m*(width (fixedLength (j*m)) f g : ℝ)^3*
        (n : ℝ)^principalExponent K k c d m := by sorry
