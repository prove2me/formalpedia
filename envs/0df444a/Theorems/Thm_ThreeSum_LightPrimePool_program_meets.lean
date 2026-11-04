-- Prove2me | Theorems.Thm_ThreeSum_LightPrimePool_program_meets
-- name    : ThreeSum.LightPrimePool.program_meets
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T11:50:57.775794+00:00
-- url     : https://prove2.me/theorems/d9174461-ba2c-4e4c-afe5-d6bbf081c2ee
-- title:
--   Light Prime Pool: program meets
-- statement:
--   The Light Prime Pool construction uses the program meets property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/LightPrimePool.lean#L267-L274
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/LightPrimePool.lean#L267-L274

import Definitions.Def_Submission_ThreeSum_LightPrimality
import Definitions.Def_Submission_ThreeSum_PrimeDensity
import Definitions.Def_Submission_ThreeSum_WeightedScore
import Mathlib.NumberTheory.Bertrand
import Definitions.Def_Submission_ThreeSum_LightPrimePool
import Theorems.Thm_ThreeSum_LightPrimality_program_meets
import Theorems.Thm_ThreeSum_LightResidueHistogram_program_meets

set_option autoImplicit false
open ThreeSum ThreeSum.LightPrimePool
open Light
set_option maxHeartbeats 1000000
set_option maxRecDepth 10000
variable {lim : Limits} {P : Program} {d : ℕ}

theorem ThreeSum.LightPrimePool.program_meets
    {μ : ℕ → ℤ} {y free : ℕ}
    (hw : (lim.space : ℤ) ≤ lim.word) (hd : d+1 < lim.depth)
    (hy : 0 < y) (hspace : space free y ≤ lim.space)
    (hword : (word y : ℤ) ≤ lim.word) :
    Meets lim program 0 d [y,free] μ (time y)
      (fun r μ' => r = (size y : ℤ) ∧ SegN μ' free (values y) ∧ Kept μ μ' free) := by sorry
