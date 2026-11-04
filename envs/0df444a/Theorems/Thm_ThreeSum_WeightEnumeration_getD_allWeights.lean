-- Prove2me | Theorems.Thm_ThreeSum_WeightEnumeration_getD_allWeights
-- name    : ThreeSum.WeightEnumeration.getD_allWeights
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T07:46:36.640354+00:00
-- url     : https://prove2.me/theorems/45be2ded-27aa-4f71-9cef-3b1843510b3f
-- title:
--   Weight Enumeration: get D all Weights
-- statement:
--   The Weight Enumeration construction uses the get D all Weights property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/WeightEnumeration.lean#L184-L188
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/WeightEnumeration.lean#L184-L188

import Definitions.Def_Submission_ThreeSum_LocalHashMoments
import Mathlib.Data.List.Range
import Definitions.Def_Submission_ThreeSum_WeightEnumeration
set_option autoImplicit false
open ThreeSum ThreeSum.WeightEnumeration
open LocalHashMoments
variable {ι K : Type*} [DecidableEq ι] [NatCast K]

theorem ThreeSum.WeightEnumeration.getD_allWeights (L p k : ℕ) (fallback : Weight L K) (hk : k < p^(2*L)) :
    (allWeights L ((List.range p).map (fun n : ℕ => (n : K)))).getD k fallback =
      decodedWeight (K := K) L p k := by sorry
