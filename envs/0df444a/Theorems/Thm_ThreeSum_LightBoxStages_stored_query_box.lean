-- Prove2me | Theorems.Thm_ThreeSum_LightBoxStages_stored_query_box
-- name    : ThreeSum.LightBoxStages.stored_query_box
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T10:17:04.174194+00:00
-- url     : https://prove2.me/theorems/fbfd206c-b389-411a-a98b-91c53b4aa913
-- title:
--   Light Box Stages: stored query box
-- statement:
--   The Light Box Stages construction uses the stored query box property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/LightBoxStages.lean#L207-L213
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/LightBoxStages.lean#L207-L213

import Definitions.Def_Submission_ThreeSum_LightZetaPass
import Definitions.Def_Submission_ThreeSum_LightDownsetSize
import Definitions.Def_Submission_ThreeSum_BoxStages
import Definitions.Def_Submission_ThreeSum_LightBoxStages
set_option autoImplicit false
open ThreeSum ThreeSum.LightBoxStages
open Light ThreeSum.SubsetAddress ThreeSum.BoxStages ThreeSum.LightZetaCell
open ThreeSum.LightPascal ThreeSum.LightSubsetAddress
variable {lim : Limits} {P : Program}

theorem ThreeSum.LightBoxStages.stored_query_box {μ : ℕ → ℤ} {L cut base : ℕ}
    {weight : Finset (Fin L) → ℤ} (h : StoredThrough μ base cut weight L)
    (q u : Finset (Fin L)) (hu : u.Nonempty) (hflags : (q \ u).card ≤ cut) :
    μ (stageBase base (downsetCap L cut) (u.min' hu).val+subsetRank (q \ u)) =
      SparseBoxes.boxSum (q \ u) (SparseBoxes.queryFree q u) weight := by sorry
