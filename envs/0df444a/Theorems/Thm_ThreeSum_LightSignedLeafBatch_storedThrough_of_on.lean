-- Prove2me | Theorems.Thm_ThreeSum_LightSignedLeafBatch_storedThrough_of_on
-- name    : ThreeSum.LightSignedLeafBatch.storedThrough_of_on
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T09:00:50.26617+00:00
-- url     : https://prove2.me/theorems/0d06017d-b02a-4a14-b632-0a67e234d70c
-- title:
--   Light Signed Leaf Batch: stored Through of on
-- statement:
--   The Light Signed Leaf Batch construction uses the stored Through of on property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/LightSignedLeafBatch.lean#L12-L24
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/LightSignedLeafBatch.lean#L12-L24

import Definitions.Def_Submission_ThreeSum_LightSignedLeafCell
import Definitions.Def_Submission_ThreeSum_MaskDecode
import Definitions.Def_Submission_ThreeSum_LightSignedLeafBatch
set_option autoImplicit false
open ThreeSum ThreeSum.LightSignedLeafBatch
open Light ThreeSum.SubsetAddress ThreeSum.LightZetaCell ThreeSum.MaskDecode
variable {lim : Limits} {P : Program}

theorem ThreeSum.LightSignedLeafBatch.storedThrough_of_on {W cut base : ℕ} {μ μ' : ℕ → ℤ}
    {f : Finset (Fin W) → ℤ}
    (h : LightZetaStages.StoredThrough μ base cut f W)
    (hkeep : ∀ i, base ≤ i → i < base+(W+1)*downsetCap W cut → μ' i = μ i) :
    LightZetaStages.StoredThrough μ' base cut f W := by sorry
