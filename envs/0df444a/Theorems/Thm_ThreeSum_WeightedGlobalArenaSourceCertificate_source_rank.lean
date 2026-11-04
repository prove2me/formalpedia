-- Prove2me | Theorems.Thm_ThreeSum_WeightedGlobalArenaSourceCertificate_source_rank
-- name    : ThreeSum.WeightedGlobalArenaSourceCertificate.source_rank
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T16:17:21.287816+00:00
-- url     : https://prove2.me/theorems/d08c9cd5-5613-4b69-bf17-cc75c5d29660
-- title:
--   Weighted Global Arena Source Certificate: source rank
-- statement:
--   The Weighted Global Arena Source Certificate construction uses the source rank property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/Weighted/Global/TernaryArenaSourceCertificate.lean#L60-L67
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/Weighted/Global/TernaryArenaSourceCertificate.lean#L60-L67

import Definitions.Def_Submission_Weighted_GlobalBank
import Definitions.Def_Submission_Weighted_Global_TernaryArenaSourceModel
import Definitions.Def_Submission_Weighted_Global_TernaryArenaSourceCertificate
import Theorems.Thm_ThreeSum_WeightedSchedule_source_rank

set_option autoImplicit false
noncomputable section
open ThreeSum ThreeSum.WeightedGlobalArenaSourceCertificate
open TernaryJointType WeightedGlobalLocalParameters WeightedGlobalCoverGoodMaps
open WeightedGlobalArenaSourceSetup TernaryCanonicalDictionaries WeightedGlobalNativeCompleteFrontend
open LightTernarySourceHost TernaryCodeSemantics
variable {p m F r : ℕ} [Fact p.Prime]
set_option maxHeartbeats 3000000

theorem ThreeSum.WeightedGlobalArenaSourceCertificate.source_rank (maps : Fin F→Weight m p) (cap : ℕ) (I : Input) (right : Bool)
    (j : ℕ) (hj : j<LightTernarySourceHost.size (source (r := r) maps cap I right).xs r) :
    WeightedGlobalBank.rank ((WeightedBankCanonical.enumeration (N m r) (cut m r)).word
      ((source (r := r) maps cap I right).key j))=r*alphaRank m := by sorry
