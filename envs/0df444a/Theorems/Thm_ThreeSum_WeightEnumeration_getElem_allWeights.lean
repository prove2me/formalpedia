-- Prove2me | Theorems.Thm_ThreeSum_WeightEnumeration_getElem_allWeights
-- name    : ThreeSum.WeightEnumeration.getElem_allWeights
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T07:46:43.718784+00:00
-- url     : https://prove2.me/theorems/dd82e2fa-0146-4588-95d9-3df67c14ce98
-- title:
--   Weight Enumeration: get Elem all Weights
-- statement:
--   The Weight Enumeration construction uses the get Elem all Weights property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/WeightEnumeration.lean#L179-L182
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/WeightEnumeration.lean#L179-L182

import Definitions.Def_Submission_ThreeSum_LocalHashMoments
import Mathlib.Data.List.Range
import Definitions.Def_Submission_ThreeSum_WeightEnumeration
set_option autoImplicit false
open ThreeSum ThreeSum.WeightEnumeration
open LocalHashMoments
variable {ι K : Type*} [DecidableEq ι] [NatCast K]

theorem ThreeSum.WeightEnumeration.getElem_allWeights (L p k : ℕ) (hk : k < p^(2*L)) :
    (allWeights L ((List.range p).map (fun n : ℕ => (n : K))))[k]'(by
      rw [allWeights_length]; exact hk) = decodedWeight (K := K) L p k := by sorry
