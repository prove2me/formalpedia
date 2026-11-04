-- Prove2me | Theorems.Thm_ThreeSum_LightParameterInit_program_meets
-- name    : ThreeSum.LightParameterInit.program_meets
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T12:25:08.586451+00:00
-- url     : https://prove2.me/theorems/5fa1f701-90fa-47de-ba21-98bc252e8763
-- title:
--   Light Parameter Init: program meets
-- statement:
--   The Light Parameter Init construction uses the program meets property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/LightParameterInit.lean#L204-L210
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/LightParameterInit.lean#L204-L210

import Definitions.Def_Submission_ThreeSum_LightScales
import Definitions.Def_Submission_ThreeSum_LightLocalParameters
import Definitions.Def_Submission_ThreeSum_LightGlobalSizes
import Definitions.Def_Submission_ThreeSum_LightParameterInit
import Theorems.Thm_ThreeSum_LightGlobalSizes_program_meets
import Theorems.Thm_ThreeSum_LightLocalCounts_program_meets
import Theorems.Thm_ThreeSum_LightLocalParameters_program_meets
import Theorems.Thm_ThreeSum_LightNatPower_program_meets
import Theorems.Thm_ThreeSum_LightPrimality_program_meets
import Theorems.Thm_ThreeSum_LightPrimePool_program_meets
import Theorems.Thm_ThreeSum_LightResidueHistogram_program_meets
import Theorems.Thm_ThreeSum_LightScales_program_meets
import Theorems.Thm_ThreeSum_LightSelectedPrime_program_meets
import Theorems.Thm_ThreeSum_LightSmallDivide_program_meets
import Theorems.Thm_ThreeSum_LightSubsetSetup_program_meets

set_option autoImplicit false
open ThreeSum ThreeSum.LightParameterInit
open Light LocalCoverBounds Scales
set_option maxHeartbeats 1500000
set_option maxRecDepth 5000
variable {lim : Limits} {P : Program} {d : ℕ}

theorem ThreeSum.LightParameterInit.program_meets {μ : ℕ → ℤ} {n dst work : ℕ}
    (hw : (lim.space : ℤ) ≤ lim.word) (hd : d+512*half n+6 ≤ lim.depth)
    (hout : dst+19 ≤ work) (hspace : space work n ≤ lim.space)
    (hword : (word n : ℤ) ≤ lim.word) :
    Meets lim program 0 d [n,dst,work] μ (time n)
      (fun r μ' => r = (radix n : ℤ) ∧ Seg μ' dst (values n) ∧
        KeptBut μ μ' work dst 19) := by sorry
