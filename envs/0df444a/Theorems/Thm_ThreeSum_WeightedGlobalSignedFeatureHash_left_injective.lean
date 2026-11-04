-- Prove2me | Theorems.Thm_ThreeSum_WeightedGlobalSignedFeatureHash_left_injective
-- name    : ThreeSum.WeightedGlobalSignedFeatureHash.left_injective
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T15:43:54.120939+00:00
-- url     : https://prove2.me/theorems/d3d55eb1-b37c-4672-a647-83b368ec0f02
-- title:
--   Weighted Global Signed Feature Hash: left injective
-- statement:
--   Distinct original integers remain distinct full signed feature vectors
--   before the row menu is applied.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/Weighted/Global/TernarySignedFeatureHash.lean#L73-L84
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/Weighted/Global/TernarySignedFeatureHash.lean#L73-L84

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

theorem ThreeSum.WeightedGlobalSignedFeatureHash.left_injective {U radix n : ℕ} (B : Fin n→ℤ)
    (hb : 1<radix) (hp : 2*radix<p) (hcap : 4*U<radix^J)
    (hB : ∀ i, |B i|≤(U : ℤ)) (hinj : Function.Injective B) :
    Function.Injective (fun i : Fin n => fun t : Fin (J+2) =>
      (feature (leftRaw U radix J (B i)) t.val : ZMod p)) := by sorry
