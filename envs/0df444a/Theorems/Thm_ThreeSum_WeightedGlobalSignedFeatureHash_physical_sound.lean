-- Prove2me | Theorems.Thm_ThreeSum_WeightedGlobalSignedFeatureHash_physical_sound
-- name    : ThreeSum.WeightedGlobalSignedFeatureHash.physical_sound
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T15:43:19.275674+00:00
-- url     : https://prove2.me/theorems/05cef019-b284-4581-8fab-5639a36534b2
-- title:
--   Weighted Global Signed Feature Hash: physical sound
-- statement:
--   The Weighted Global Signed Feature Hash construction uses the physical sound property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/Weighted/Global/TernarySignedFeatureHash.lean#L56-L69
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/Weighted/Global/TernarySignedFeatureHash.lean#L56-L69

import Definitions.Def_Submission_Weighted_GlobalBank
import Definitions.Def_Submission_ThreeSum_TernaryOriginalKeyCodes
import Definitions.Def_Submission_Weighted_Global_TernaryNativeRequesterCoverage
import Definitions.Def_Submission_ThreeSum_TernarySignedModes
import Definitions.Def_Submission_Weighted_Global_TernarySignedFeatureHash
set_option autoImplicit false
noncomputable section
open ThreeSum ThreeSum.WeightedGlobalSignedFeatureHash
open TernarySignedReduction TernarySignedLayout WeightedGlobalNativeRequesterCoverage
variable {p J r : ℕ} [Fact p.Prime]

theorem ThreeSum.WeightedGlobalSignedFeatureHash.physical_sound {U radix : ℕ} {b c b' c' : ℤ}
    (hb : 1<radix) (hp : 2*radix<p)
    (hB : |b|≤(U : ℤ)) (hC : |c|≤(U : ℤ)) (hB' : |b'|≤(U : ℤ)) (hC' : |c'|≤(U : ℤ))
    (hcap : 4*U<radix^J)
    (he : (fun i : Fin (J+2) => (feature (leftRaw U radix J b) i.val : ZMod p))+
      (fun i => (feature (rightRaw U radix J c) i.val : ZMod p))=
      (fun i : Fin (J+2) => (feature (leftRaw U radix J b') i.val : ZMod p))+
      (fun i => (feature (rightRaw U radix J c') i.val : ZMod p))) : c-b=c'-b' := by sorry
