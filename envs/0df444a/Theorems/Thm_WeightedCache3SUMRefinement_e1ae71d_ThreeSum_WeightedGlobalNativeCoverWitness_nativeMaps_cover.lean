-- Prove2me | Theorems.Thm_WeightedCache3SUMRefinement_e1ae71d_ThreeSum_WeightedGlobalNativeCoverWitness_nativeMaps_cover
-- name    : WeightedCache3SUMRefinement_e1ae71d.ThreeSum.WeightedGlobalNativeCoverWitness.nativeMaps_cover
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-04T10:28:11.834338+00:00
-- url     : https://prove2.me/theorems/5a99f21a-91c1-4b15-854c-4d82199ff6e6
-- title:
--   nativeMaps_cover
-- statement:
--   Refined weighted-cache 3SUM lemma. Its formal statement preserves the complete source hypotheses and conclusion.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/e1ae71db2231f172c6541820e2ce0a54aa14fc64/Submission/Weighted/Global/TernaryNativeCoverWitness.lean#L110-L122
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/e1ae71db2231f172c6541820e2ce0a54aa14fc64/Submission/Weighted/Global/TernaryNativeCoverWitness.lean#L110-L122

import Definitions.Def_WeightedCache3SUMRefinement_e1ae71d_Submission_Weighted_GlobalBank
import Definitions.Def_WeightedCache3SUMRefinement_e1ae71d_Submission_Weighted_Global_TernaryOversizePrime
import Definitions.Def_Submission_ThreeSum_TernaryCanonicalDictionaries
import Definitions.Def_Submission_ThreeSum_TernaryOriginalKeyCodes
import Definitions.Def_WeightedCache3SUMRefinement_e1ae71d_Submission_Weighted_Global_TernaryNativeCoverWitness
set_option autoImplicit false
open WeightedCache3SUMRefinement_e1ae71d
open _root_.ThreeSum
noncomputable section
open WeightedCache3SUMRefinement_e1ae71d.ThreeSum WeightedCache3SUMRefinement_e1ae71d.ThreeSum.WeightedGlobalNativeCoverWitness
open Finset TernaryJointType TernaryCoverLocal WeightedGlobalLocalParameters
open WeightedGlobalCoverGoodMaps WeightedGlobalCoverFrequency TernaryFixedDictionaries
open TernaryCanonicalDictionaries
variable {m p : ℕ} [Fact p.Prime]
variable {I : Type*} [Fintype I] [DecidableEq I]
set_option maxHeartbeats 3000000
open WeightedGlobalOversizePrime

theorem WeightedCache3SUMRefinement_e1ae71d.ThreeSum.WeightedGlobalNativeCoverWitness.nativeMaps_cover {K m k : ℕ} (hK : 0<K) (hm : 0<m) (hk : 0<k)
    (a b : ZMod (nativePrime K m)) :
    ∃ i : Fin (nativeFamily K m k).length,
      Covers m (nativePrime K m) (WeightedGlobalCoverCapParameters.sourceCap m (nativePrime K m))
        (WeightedGlobalCoverCapParameters.rawThreshold (nativePrime K m)
          (WeightedGlobalCoverCapParameters.sourceCap m (nativePrime K m)) k)
        (nativeMaps K m k i) (a,b) := by sorry
