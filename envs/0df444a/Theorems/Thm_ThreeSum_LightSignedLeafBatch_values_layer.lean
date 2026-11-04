-- Prove2me | Theorems.Thm_ThreeSum_LightSignedLeafBatch_values_layer
-- name    : ThreeSum.LightSignedLeafBatch.values_layer
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T09:03:15.719608+00:00
-- url     : https://prove2.me/theorems/062dcebc-c246-4c7d-abde-ddd71e835015
-- title:
--   Light Signed Leaf Batch: values layer
-- statement:
--   The Light Signed Leaf Batch construction uses the values layer property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/LightSignedLeafBatch.lean#L151-L156
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/LightSignedLeafBatch.lean#L151-L156

import Definitions.Def_Submission_ThreeSum_LightSignedLeafCell
import Definitions.Def_Submission_ThreeSum_MaskDecode
import Definitions.Def_Submission_ThreeSum_LightSignedLeafBatch
import Theorems.Thm_ThreeSum_LightZetaBatch_values_layer

set_option autoImplicit false
open ThreeSum ThreeSum.LightSignedLeafBatch
open Light ThreeSum.SubsetAddress ThreeSum.LightZetaCell ThreeSum.MaskDecode
variable {lim : Limits} {P : Program}

theorem ThreeSum.LightSignedLeafBatch.values_layer {W cardinal : ℕ} (μ : ℕ → ℤ) (dst : ℕ)
    (weight : Finset (Fin W) → ℤ) (S : Finset (Fin W)) :
    values μ dst (enumerateLayer W cardinal) weight S =
      if S.card = cardinal then weight S else μ (dst+subsetRank S) := by sorry
