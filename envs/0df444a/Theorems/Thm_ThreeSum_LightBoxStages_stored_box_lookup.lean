-- Prove2me | Theorems.Thm_ThreeSum_LightBoxStages_stored_box_lookup
-- name    : ThreeSum.LightBoxStages.stored_box_lookup
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T09:03:09.229803+00:00
-- url     : https://prove2.me/theorems/22792c58-329a-42d2-9527-3292fb27dcae
-- title:
--   Light Box Stages: stored box lookup
-- statement:
--   The Light Box Stages construction uses the stored box lookup property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/LightBoxStages.lean#L199-L205
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/LightBoxStages.lean#L199-L205

import Definitions.Def_Submission_ThreeSum_LightZetaPass
import Definitions.Def_Submission_ThreeSum_LightDownsetSize
import Definitions.Def_Submission_ThreeSum_BoxStages
import Definitions.Def_Submission_ThreeSum_LightBoxStages
set_option autoImplicit false
open ThreeSum ThreeSum.LightBoxStages
open Light ThreeSum.SubsetAddress ThreeSum.BoxStages ThreeSum.LightZetaCell
open ThreeSum.LightPascal ThreeSum.LightSubsetAddress
variable {lim : Limits} {P : Program}

theorem ThreeSum.LightBoxStages.stored_box_lookup {μ : ℕ → ℤ} {L cut base j : ℕ}
    {weight : Finset (Fin L) → ℤ} (h : StoredThrough μ base cut weight L) (hj : j ≤ L)
    (flags : Finset (Fin L)) (hflags : flags.card ≤ cut) :
    μ (stageBase base (downsetCap L cut) j+subsetRank flags) =
      SparseBoxes.boxSum flags (flags ∩ initialCoords L j) weight := by sorry
