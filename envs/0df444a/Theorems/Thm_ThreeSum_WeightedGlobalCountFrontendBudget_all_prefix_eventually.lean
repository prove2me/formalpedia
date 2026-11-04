-- Prove2me | Theorems.Thm_ThreeSum_WeightedGlobalCountFrontendBudget_all_prefix_eventually
-- name    : ThreeSum.WeightedGlobalCountFrontendBudget.all_prefix_eventually
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T13:17:11.719567+00:00
-- url     : https://prove2.me/theorems/a60057b2-32cd-4f56-b475-40f927ec7841
-- title:
--   Weighted Global Count Frontend Budget: all prefix eventually
-- statement:
--   Uniform, genuine all-prefix natural time bound for the physical frontend,
--   including polynomial channel overhead, strictly below the requested 1.921.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/Weighted/Global/CountFrontendBudget.lean#L407-L434
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/Weighted/Global/CountFrontendBudget.lean#L407-L434

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

theorem ThreeSum.WeightedGlobalCountFrontendBudget.all_prefix_eventually {K m b C A degree : ℕ}
    (hK : 100000000000000000000≤K) (c d : ℕ) (hb : b≤c*(fixedLength m+1)^d)
    (hgood : GoodBlock K m)
    (hover : overheadCharge (selectedMoment K) c d m<microAllowance K)
    (f g : ℕ→ℕ→Config) (groups wanted : ℕ→ℕ→ℕ) (channels : ℕ→ℕ)
    (hT : ∀ n, 1<n → ∀ j≤radixLength m n, (f n j).T=bankCut m j)
    (hgroups : ∀ n, 1<n → ∀ j≤radixLength m n, groups n j≤
      (b*(nativeFamily K m (selectedMoment K)).length*
        rawThreshold (nativePrime K m) (sourceCap m (nativePrime K m)) (selectedMoment K))^j)
    (hwanted : ∀ n, 1<n → ∀ j≤radixLength m n, (wanted n j : ℝ)≤
      (n : ℝ)*((nativePrime K m : ℝ)/partitionCap m)^j*
        ((b*(nativeFamily K m (selectedMoment K)).length*
          rawThreshold (nativePrime K m) (sourceCap m (nativePrime K m)) (selectedMoment K) : ℕ) : ℝ)^j)
    (hwidth : ∀ n, 1<n → ∀ j≤radixLength m n,
      width (fixedLength (j*m)) (f n j) (g n j)≤C*(radixLength m n+1))
    (hchannels : ∀ n, 1<n → channels n≤A*(radixLength m n+1)^degree) :
    ∀ᶠ n : ℕ in atTop, (allPrefixTime m f g groups wanted channels n : ℝ)≤(n : ℝ)^frontendExponent := by sorry
