-- Prove2me | Theorems.Thm_ThreeSum_LightZetaStages_stored_zeta
-- name    : ThreeSum.LightZetaStages.stored_zeta
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T11:03:30.43704+00:00
-- url     : https://prove2.me/theorems/fea80ba6-3d64-4def-bd71-15bf4497c79c
-- title:
--   Light Zeta Stages: stored zeta
-- statement:
--   The Light Zeta Stages construction uses the stored zeta property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/LightZetaStages.lean#L197-L200
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/LightZetaStages.lean#L197-L200

import Definitions.Def_Submission_ThreeSum_LightZetaPass
import Definitions.Def_Submission_ThreeSum_LightDownsetSize
import Definitions.Def_Submission_ThreeSum_SubsetStages
import Definitions.Def_Submission_ThreeSum_LightZetaStages
set_option autoImplicit false
open ThreeSum ThreeSum.LightZetaStages
open Light ThreeSum.SubsetAddress ThreeSum.SubsetStages ThreeSum.LightZetaCell
open ThreeSum.LightPascal ThreeSum.LightSubsetAddress
variable {lim : Limits} {P : Program}

theorem ThreeSum.LightZetaStages.stored_zeta {μ : ℕ → ℤ} {L cut base : ℕ} {f : Finset (Fin L) → ℤ}
    (h : StoredThrough μ base cut f L) :
    TableAt μ (stageBase base (downsetCap L cut) L) cut (Subset.zeta f) := by sorry
