-- Prove2me | Theorems.Thm_ThreeSum_WeightedGlobalSignedFeatureHash_right_injective
-- name    : ThreeSum.WeightedGlobalSignedFeatureHash.right_injective
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T15:48:01.954346+00:00
-- url     : https://prove2.me/theorems/bc78b5ef-494f-47ac-9c6f-52f8125deae7
-- title:
--   Weighted Global Signed Feature Hash: right injective
-- statement:
--   The Weighted Global Signed Feature Hash construction uses the right injective property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/Weighted/Global/TernarySignedFeatureHash.lean#L86-L97
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/Weighted/Global/TernarySignedFeatureHash.lean#L86-L97

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

theorem ThreeSum.WeightedGlobalSignedFeatureHash.right_injective {U radix n : ℕ} (C : Fin n→ℤ)
    (hb : 1<radix) (hp : 2*radix<p) (hcap : 4*U<radix^J)
    (hC : ∀ i, |C i|≤(U : ℤ)) (hinj : Function.Injective C) :
    Function.Injective (fun i : Fin n => fun t : Fin (J+2) =>
      (feature (rightRaw U radix J (C i)) t.val : ZMod p)) := by sorry
