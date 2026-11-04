-- Prove2me | Theorems.Thm_ThreeSum_LightSourceStages_source_abs_le
-- name    : ThreeSum.LightSourceStages.source_abs_le
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T08:53:17.638477+00:00
-- url     : https://prove2.me/theorems/ab99704e-0a1d-4431-bf58-c5916ad479b3
-- title:
--   Light Source Stages: source abs le
-- statement:
--   The Light Source Stages construction uses the source abs le property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/LightSourceStages.lean#L75-L83
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/LightSourceStages.lean#L75-L83

import Definitions.Def_Submission_ThreeSum_LightSourceBuild
import Definitions.Def_Submission_ThreeSum_SourceTableLayout
import Definitions.Def_Submission_ThreeSum_LightZetaStages
import Definitions.Def_Submission_ThreeSum_LightSourceStages
set_option autoImplicit false
open ThreeSum ThreeSum.LightSourceStages
open Light SubsetAddress LightSubsetAddress LightPascal LightZetaCell
set_option maxHeartbeats 2200000
set_option maxRecDepth 12000
variable {lim : Limits} {P : Program} {d : ℕ}

theorem ThreeSum.LightSourceStages.source_abs_le {L : ℕ} (μ : ℕ → ℤ) (src N p m : ℕ) (shift : ℤ)
    (endpoint : Finset (Fin L) → ℤ) (flag : Finset (Fin L) → ℕ)
    (S : Finset (Fin L)) : |source μ src N p m shift endpoint flag S| ≤ (N : ℤ) := by sorry
