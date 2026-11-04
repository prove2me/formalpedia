-- Prove2me | Theorems.Thm_ThreeSum_LightEncodedColorLayout_program_meets
-- name    : ThreeSum.LightEncodedColorLayout.program_meets
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T14:04:01.820411+00:00
-- url     : https://prove2.me/theorems/7d9c9d73-872c-4e0e-86eb-7df5961ba0d6
-- title:
--   Light Encoded Color Layout: program meets
-- statement:
--   The Light Encoded Color Layout construction uses the program meets property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/LightEncodedColorLayout.lean#L143-L149
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/LightEncodedColorLayout.lean#L143-L149

import Definitions.Def_Submission_ThreeSum_EncodedColorLayout
import Definitions.Def_Submission_ThreeSum_LightEncodedColorLayout
import Theorems.Thm_ThreeSum_LightBandCandidates_program_meets
import Theorems.Thm_ThreeSum_LightBandEnumeration_program_meets
import Theorems.Thm_ThreeSum_LightBandLookup_program_meets
import Theorems.Thm_ThreeSum_LightBandPartition_program_meets
import Theorems.Thm_ThreeSum_LightBandPreprocessing_program_meets
import Definitions.Def_WeightedCache3SUM_Alias_4c7c7c4548f5a674
import Theorems.Thm_ThreeSum_LightBandPrimeConstruction_program_meets
import Theorems.Thm_ThreeSum_LightBandPrimeDepth_program_meets
import Definitions.Def_WeightedCache3SUM_Alias_7e2b05f783284e0e
import Theorems.Thm_ThreeSum_LightBandRawACatalog_program_meets
import Theorems.Thm_ThreeSum_LightBandRawAColor_program_meets
import Theorems.Thm_ThreeSum_LightBandRawA_program_meets
import Theorems.Thm_ThreeSum_LightBandWeightedScoreSlice_program_meets
import Definitions.Def_WeightedCache3SUM_Alias_2ea73ff18fd48136
import Theorems.Thm_ThreeSum_LightBlockCoefficients_program_meets
import Theorems.Thm_ThreeSum_LightBooleanDot_program_meets
import Theorems.Thm_ThreeSum_LightCapacity_program_meets
import Theorems.Thm_ThreeSum_LightClassFilter_program_meets
import Theorems.Thm_ThreeSum_LightColorArray_program_meets
import Theorems.Thm_ThreeSum_LightColorBands_program_meets
import Theorems.Thm_ThreeSum_LightColorClasses_program_meets
import Theorems.Thm_ThreeSum_LightColorIndex_program_meets
import Theorems.Thm_ThreeSum_LightCyclic_program_meets
import Theorems.Thm_ThreeSum_LightHeaderBands_program_meets
import Theorems.Thm_ThreeSum_LightKaratsuba_program_meets
import Theorems.Thm_ThreeSum_LightLookupSum_program_meets
import Theorems.Thm_ThreeSum_LightMaskBits_program_meets
import Theorems.Thm_ThreeSum_LightMaskErase_program_meets
import Theorems.Thm_ThreeSum_LightMaskHashes_program_meets
import Theorems.Thm_ThreeSum_LightModuloCounts_program_meets
import Theorems.Thm_ThreeSum_LightNormalize_program_meets
import Theorems.Thm_ThreeSum_LightOneHot_program_meets
import Theorems.Thm_ThreeSum_LightPrimality_program_meets
import Theorems.Thm_ThreeSum_LightPrimeChain_program_meets
import Theorems.Thm_ThreeSum_LightPrimeMinimum_program_meets
import Theorems.Thm_ThreeSum_LightPrimePool_program_meets
import Theorems.Thm_ThreeSum_LightResidueHistogram_program_meets
import Theorems.Thm_ThreeSum_LightScaleArray_program_meets
import Theorems.Thm_ThreeSum_LightSmallDivide_program_meets
import Theorems.Thm_ThreeSum_LightSortedBands_program_meets
import Theorems.Thm_ThreeSum_LightWeightedScore_program_meets

set_option autoImplicit false
open ThreeSum ThreeSum.LightEncodedColorLayout
open Light BandPartition EncodedColorLayout
set_option maxHeartbeats 2200000
set_option maxRecDepth 11000
variable {lim : Limits} {P : Program} {d : ℕ}

theorem ThreeSum.LightEncodedColorLayout.program_meets {n g free : ℕ} {μ : ℕ → ℤ}
    (hw : (lim.space : ℤ) ≤ lim.word) (hn : 0 < n) (hg : 0 < g)
    (hspace : normalizedEnd free n g+1 ≤ lim.space)
    (hword : (word n g : ℤ) ≤ lim.word) (hd : d < lim.depth) :
    Meets lim program 0 d [n,g,free] μ (time n g)
      (fun r ν => r=(normalizedEnd free n g : ℤ) ∧ Seg ν free (normalizedHeads free n g) ∧ Kept μ ν free) := by sorry
