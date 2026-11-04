-- Prove2me | Theorems.Thm_ThreeSum_LightWantedJoin_program_meets
-- name    : ThreeSum.LightWantedJoin.program_meets
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T12:12:55.809388+00:00
-- url     : https://prove2.me/theorems/1b9cca3f-7de5-459e-bbdd-c4f1010d967a
-- title:
--   Light Wanted Join: program meets
-- statement:
--   The Light Wanted Join construction uses the program meets property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/LightWantedJoin.lean#L140-L150
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/LightWantedJoin.lean#L140-L150

import Definitions.Def_Submission_ThreeSum_LightWantedRow
import Definitions.Def_Submission_ThreeSum_WantedPairs
import Definitions.Def_Submission_ThreeSum_LightWantedJoin
import Theorems.Thm_ThreeSum_LightBalancedOffset_program_meets
import Theorems.Thm_ThreeSum_LightBlockCoefficients_program_meets
import Theorems.Thm_ThreeSum_LightBooleanDot_program_meets
import Theorems.Thm_ThreeSum_LightCapacity_program_meets
import Theorems.Thm_ThreeSum_LightCyclic_program_meets
import Theorems.Thm_ThreeSum_LightKaratsuba_program_meets
import Theorems.Thm_ThreeSum_LightLookupSum_program_meets
import Theorems.Thm_ThreeSum_LightMaskBits_program_meets
import Theorems.Thm_ThreeSum_LightMaskErase_program_meets
import Theorems.Thm_ThreeSum_LightMaskHashes_program_meets
import Theorems.Thm_ThreeSum_LightModuloCounts_program_meets
import Theorems.Thm_ThreeSum_LightOneHot_program_meets
import Theorems.Thm_ThreeSum_LightOriginalOffset_program_meets
import Theorems.Thm_ThreeSum_LightResidueHistogram_program_meets
import Theorems.Thm_ThreeSum_LightScaleArray_program_meets
set_option autoImplicit false
open ThreeSum ThreeSum.LightWantedJoin
open Light SourceBuckets WantedPairs
set_option maxHeartbeats 1800000
set_option maxRecDepth 10000
variable {lim : Limits} {P : Program}

theorem ThreeSum.LightWantedJoin.program_meets {keys offsets flat NR M dst n d : ℕ} {μ : ℕ → ℤ} (left right : ℕ → ℕ)
    (hright : ∀ j < NR, right j < M) (hw : (lim.space : ℤ) ≤ lim.word) (hkeys : keys + n ≤ dst)
    (hoffsets : offsets + M + 1 ≤ dst) (hflat : flat + NR ≤ dst) (hspace : dst + 2 * count left right NR n ≤ lim.space)
    (hd : d + n + 2 ≤ lim.depth) (hleft : ∀ i < n, left i < M) (hread : ∀ i < n, μ (keys + i) = (left i : ℤ))
    (H : Stored μ right NR M offsets flat) :
    Meets lim program 0 d [keys, offsets, flat, n, NR, M, dst] μ (time left right NR n)
      (fun r ν => r = (count left right NR n : ℤ) ∧ Seg ν dst (cells (pairs μ offsets flat left n)) ∧ Kept μ ν dst) := by sorry
