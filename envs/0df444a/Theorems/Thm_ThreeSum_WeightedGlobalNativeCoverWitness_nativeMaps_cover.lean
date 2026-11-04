-- Prove2me | Theorems.Thm_ThreeSum_WeightedGlobalNativeCoverWitness_nativeMaps_cover
-- name    : ThreeSum.WeightedGlobalNativeCoverWitness.nativeMaps_cover
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T10:06:46.321744+00:00
-- url     : https://prove2.me/theorems/d2410be1-f3f4-4efd-b9b6-0f35e58c2760
-- title:
--   Weighted Global Native Cover Witness: native Maps cover
-- statement:
--   The Weighted Global Native Cover Witness construction uses the native Maps cover property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/Weighted/Global/TernaryNativeCoverWitness.lean#L110-L122
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/Weighted/Global/TernaryNativeCoverWitness.lean#L110-L122

import Definitions.Def_Submission_Weighted_GlobalBank
import Definitions.Def_Submission_Weighted_Global_TernaryOversizePrime
import Definitions.Def_Submission_ThreeSum_TernaryCanonicalDictionaries
import Definitions.Def_Submission_ThreeSum_TernaryOriginalKeyCodes
import Definitions.Def_Submission_Weighted_Global_TernaryNativeCoverWitness
set_option autoImplicit false
noncomputable section
open ThreeSum ThreeSum.WeightedGlobalNativeCoverWitness
open Finset TernaryJointType TernaryCoverLocal WeightedGlobalLocalParameters
open WeightedGlobalCoverGoodMaps WeightedGlobalCoverFrequency TernaryFixedDictionaries
open TernaryCanonicalDictionaries
variable {m p : ℕ} [Fact p.Prime]
variable {I : Type*} [Fintype I] [DecidableEq I]
set_option maxHeartbeats 3000000
open WeightedGlobalOversizePrime

theorem ThreeSum.WeightedGlobalNativeCoverWitness.nativeMaps_cover {K m k : ℕ} (hK : 0<K) (hm : 0<m) (hk : 0<k)
    (a b : ZMod (nativePrime K m)) :
    ∃ i : Fin (nativeFamily K m k).length,
      Covers m (nativePrime K m) (WeightedGlobalCoverCapParameters.sourceCap m (nativePrime K m))
        (WeightedGlobalCoverCapParameters.rawThreshold (nativePrime K m)
          (WeightedGlobalCoverCapParameters.sourceCap m (nativePrime K m)) k)
        (nativeMaps K m k i) (a,b) := by sorry
