-- Prove2me | Theorems.Thm_ThreeSum_WeightedGlobalArenaSourceCertificate_source_factorial
-- name    : ThreeSum.WeightedGlobalArenaSourceCertificate.source_factorial
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T16:15:42.745894+00:00
-- url     : https://prove2.me/theorems/cf77f730-90d4-4ebf-95f6-7d9012b1823c
-- title:
--   Weighted Global Arena Source Certificate: source factorial
-- statement:
--   The Weighted Global Arena Source Certificate construction uses the source factorial property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/Weighted/Global/TernaryArenaSourceCertificate.lean#L52-L58
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/Weighted/Global/TernaryArenaSourceCertificate.lean#L52-L58

import Definitions.Def_Submission_Weighted_GlobalBank
import Definitions.Def_Submission_Weighted_Global_TernaryArenaSourceModel
import Definitions.Def_Submission_Weighted_Global_TernaryArenaSourceCertificate
set_option autoImplicit false
noncomputable section
open ThreeSum ThreeSum.WeightedGlobalArenaSourceCertificate
open TernaryJointType WeightedGlobalLocalParameters WeightedGlobalCoverGoodMaps
open WeightedGlobalArenaSourceSetup TernaryCanonicalDictionaries WeightedGlobalNativeCompleteFrontend
open LightTernarySourceHost TernaryCodeSemantics
variable {p m F r : ℕ} [Fact p.Prime]
set_option maxHeartbeats 3000000

theorem ThreeSum.WeightedGlobalArenaSourceCertificate.source_factorial (maps : Fin F→Weight m p) (cap : ℕ) (I : Input) (right : Bool)
    (j : ℕ) (hj : j<LightTernarySourceHost.size (source (r := r) maps cap I right).xs r) :
    ((source (r := r) maps cap I right).factor : ℤ)=
      TernaryConvolution.factorial ((WeightedBankCanonical.enumeration (N m r) (cut m r)).word
        ((source (r := r) maps cap I right).key j)) := by sorry
