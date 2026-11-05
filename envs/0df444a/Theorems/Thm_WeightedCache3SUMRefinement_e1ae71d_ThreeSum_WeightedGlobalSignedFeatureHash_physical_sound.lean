-- Prove2me | Theorems.Thm_WeightedCache3SUMRefinement_e1ae71d_ThreeSum_WeightedGlobalSignedFeatureHash_physical_sound
-- name    : WeightedCache3SUMRefinement_e1ae71d.ThreeSum.WeightedGlobalSignedFeatureHash.physical_sound
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-04T12:41:28.760332+00:00
-- url     : https://prove2.me/theorems/3fc148ab-bd96-42fa-a527-7494be2dc8f9
-- title:
--   physical_sound
-- statement:
--   Refined weighted-cache 3SUM lemma. Its formal statement preserves the complete source hypotheses and conclusion.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/e1ae71db2231f172c6541820e2ce0a54aa14fc64/Submission/Weighted/Global/TernarySignedFeatureHash.lean#L56-L69
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/e1ae71db2231f172c6541820e2ce0a54aa14fc64/Submission/Weighted/Global/TernarySignedFeatureHash.lean#L56-L69

import Definitions.Def_WeightedCache3SUMRefinement_e1ae71d_Submission_Weighted_GlobalBank
import Definitions.Def_Submission_ThreeSum_TernaryOriginalKeyCodes
import Definitions.Def_WeightedCache3SUMRefinement_e1ae71d_Submission_Weighted_Global_TernaryNativeRequesterCoverage
import Definitions.Def_Submission_ThreeSum_TernarySignedModes
import Definitions.Def_WeightedCache3SUMRefinement_e1ae71d_Submission_Weighted_Global_TernarySignedFeatureHash
set_option autoImplicit false
open WeightedCache3SUMRefinement_e1ae71d
open _root_.ThreeSum
noncomputable section
open WeightedCache3SUMRefinement_e1ae71d.ThreeSum WeightedCache3SUMRefinement_e1ae71d.ThreeSum.WeightedGlobalSignedFeatureHash
open TernarySignedReduction TernarySignedLayout WeightedGlobalNativeRequesterCoverage
variable {p J r : ℕ} [Fact p.Prime]

theorem WeightedCache3SUMRefinement_e1ae71d.ThreeSum.WeightedGlobalSignedFeatureHash.physical_sound {U radix : ℕ} {b c b' c' : ℤ}
    (hb : 1<radix) (hp : 2*radix<p)
    (hB : |b|≤(U : ℤ)) (hC : |c|≤(U : ℤ)) (hB' : |b'|≤(U : ℤ)) (hC' : |c'|≤(U : ℤ))
    (hcap : 4*U<radix^J)
    (he : (fun i : Fin (J+2) => (feature (leftRaw U radix J b) i.val : ZMod p))+
      (fun i => (feature (rightRaw U radix J c) i.val : ZMod p))=
      (fun i : Fin (J+2) => (feature (leftRaw U radix J b') i.val : ZMod p))+
      (fun i => (feature (rightRaw U radix J c') i.val : ZMod p))) : c-b=c'-b' := by sorry
