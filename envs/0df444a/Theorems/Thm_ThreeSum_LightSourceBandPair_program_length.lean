-- Prove2me | Theorems.Thm_ThreeSum_LightSourceBandPair_program_length
-- name    : ThreeSum.LightSourceBandPair.program_length
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T12:24:18.562324+00:00
-- url     : https://prove2.me/theorems/2fb440bf-3724-4498-ac04-7d31d7a4883b
-- title:
--   Light Source Band Pair: program length
-- statement:
--   The Light Source Band Pair construction uses the program length property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/LightSourceBandPair.lean#L186-L186
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/LightSourceBandPair.lean#L186-L186

import Definitions.Def_Submission_ThreeSum_LightSourceBandProgram
import Definitions.Def_Submission_ThreeSum_SourceBandPairData
import Definitions.Def_Submission_ThreeSum_LightSortedBands
import Definitions.Def_Submission_ThreeSum_LightSourceBandPair
import Theorems.Thm_ThreeSum_LightBlockSourceBatchProgram_program_length
import Theorems.Thm_ThreeSum_LightBlockSourceCatalogProgram_program_length
import Theorems.Thm_ThreeSum_LightBlockSourceRetainedProgram_program_length
import Theorems.Thm_ThreeSum_LightSourceBandProgram_program_length
import Theorems.Thm_ThreeSum_LightSourceBucketOriginal_program_length
import Theorems.Thm_ThreeSum_LightSourceOccurrenceArray_program_length
import Theorems.Thm_ThreeSum_LightSourceRetainedStages_program_length

set_option autoImplicit false
open ThreeSum ThreeSum.LightSourceBandPair
open Light BandPartition SourceBandPairData
set_option maxHeartbeats 3000000
set_option maxRecDepth 18000
variable {lim : Limits} {P : Program} {d : ℕ}

theorem ThreeSum.LightSourceBandPair.program_length : program.length=14 := by sorry
