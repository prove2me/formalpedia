-- Prove2me | Theorems.Thm_WeightedCache3SUMRefinement_e1ae71d_ThreeSum_WeightedGlobalNativeCoverWitness_local_record_witness
-- name    : WeightedCache3SUMRefinement_e1ae71d.ThreeSum.WeightedGlobalNativeCoverWitness.local_record_witness
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-04T10:28:31.434274+00:00
-- url     : https://prove2.me/theorems/def56768-69c7-4c3a-ad35-ce181f9f95b2
-- title:
--   local_record_witness
-- statement:
--   Refined weighted-cache 3SUM lemma. Its formal statement preserves the complete source hypotheses and conclusion.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/e1ae71db2231f172c6541820e2ce0a54aa14fc64/Submission/Weighted/Global/TernaryNativeCoverWitness.lean#L47-L72
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/e1ae71db2231f172c6541820e2ce0a54aa14fc64/Submission/Weighted/Global/TernaryNativeCoverWitness.lean#L47-L72

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

theorem WeightedCache3SUMRefinement_e1ae71d.ThreeSum.WeightedGlobalNativeCoverWitness.local_record_witness (maps : I → Weight m p) (B τ : ℕ)
    (hcover : ∀ a b : ZMod p, ∃ i, Covers m p B τ (maps i) (a,b)) (a b : ZMod p) :
    ∃ i : I, ∃ e : ActualEdge m,
      maps i∉rawBadMaps m p τ ∧
      leftRecord i e∈records false maps B ∧ rightRecord i e∈records true maps B ∧
      leftNative maps (leftRecord i e)=a ∧ rightNative maps (rightRecord i e)=b ∧
      outputHash (maps i) (output e)=a+b := by sorry
