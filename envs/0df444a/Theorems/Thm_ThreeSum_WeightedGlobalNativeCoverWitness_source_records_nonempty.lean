-- Prove2me | Theorems.Thm_ThreeSum_WeightedGlobalNativeCoverWitness_source_records_nonempty
-- name    : ThreeSum.WeightedGlobalNativeCoverWitness.source_records_nonempty
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T09:38:00.942139+00:00
-- url     : https://prove2.me/theorems/99f06a1b-022c-454f-984a-1b842a18092d
-- title:
--   Weighted Global Native Cover Witness: source records nonempty
-- statement:
--   The Weighted Global Native Cover Witness construction uses the source records nonempty property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/Weighted/Global/TernaryNativeCoverWitness.lean#L92-L103
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/Weighted/Global/TernaryNativeCoverWitness.lean#L92-L103

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

theorem ThreeSum.WeightedGlobalNativeCoverWitness.source_records_nonempty (maps : I → Weight m p) (B τ : ℕ)
    (hcover : ∀ a b : ZMod p, ∃ i, Covers m p B τ (maps i) (a,b)) :
    0<(records (α := fixedAlpha m) false maps B).length ∧
      0<(records (α := fixedAlpha m) true maps B).length := by sorry
