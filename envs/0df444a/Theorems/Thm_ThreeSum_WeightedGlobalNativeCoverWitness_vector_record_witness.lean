-- Prove2me | Theorems.Thm_ThreeSum_WeightedGlobalNativeCoverWitness_vector_record_witness
-- name    : ThreeSum.WeightedGlobalNativeCoverWitness.vector_record_witness
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T10:06:51.387036+00:00
-- url     : https://prove2.me/theorems/b920df78-2363-4817-a4ff-9a5ee0fcdf99
-- title:
--   Weighted Global Native Cover Witness: vector record witness
-- statement:
--   A full native-coordinate vector has one retained local choice in every
--   coordinate. The list retains map occurrences, source words, and output type.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/Weighted/Global/TernaryNativeCoverWitness.lean#L76-L89
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/Weighted/Global/TernaryNativeCoverWitness.lean#L76-L89

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

theorem ThreeSum.WeightedGlobalNativeCoverWitness.vector_record_witness (maps : I → Weight m p) (B τ : ℕ)
    (hcover : ∀ a b : ZMod p, ∃ i, Covers m p B τ (maps i) (a,b))
    {r : ℕ} (a b : Fin r → ZMod p) :
    ∃ occurrence : Fin r → I, ∃ edge : Fin r → ActualEdge m,
      ∀ j, maps (occurrence j)∉rawBadMaps m p τ ∧
        leftRecord (occurrence j) (edge j)∈records false maps B ∧
        rightRecord (occurrence j) (edge j)∈records true maps B ∧
        leftNative maps (leftRecord (occurrence j) (edge j))=a j ∧
        rightNative maps (rightRecord (occurrence j) (edge j))=b j ∧
        outputHash (maps (occurrence j)) (output (edge j))=a j+b j := by sorry
