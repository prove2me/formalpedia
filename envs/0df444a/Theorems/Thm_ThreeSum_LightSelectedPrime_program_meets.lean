-- Prove2me | Theorems.Thm_ThreeSum_LightSelectedPrime_program_meets
-- name    : ThreeSum.LightSelectedPrime.program_meets
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T12:01:36.596724+00:00
-- url     : https://prove2.me/theorems/de9ef2af-251a-4f02-bba3-f2a4a4f1b03e
-- title:
--   Light Selected Prime: program meets
-- statement:
--   The Light Selected Prime construction uses the program meets property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/LightSelectedPrime.lean#L104-L111
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/LightSelectedPrime.lean#L104-L111

import Definitions.Def_Submission_ThreeSum_LightPrimePool
import Definitions.Def_Submission_ThreeSum_LocalCoverBounds
import Definitions.Def_Submission_ThreeSumApsp_Lang_Lib_Sqrt
import Definitions.Def_Submission_ThreeSum_LightSelectedPrime
import Theorems.Thm_ThreeSum_LightPrimality_program_meets
import Theorems.Thm_ThreeSum_LightPrimePool_program_meets
import Theorems.Thm_ThreeSum_LightResidueHistogram_program_meets

set_option autoImplicit false
open ThreeSum ThreeSum.LightSelectedPrime
open Light LocalCoverBounds LightResidues
set_option maxHeartbeats 1000000
variable {lim : Limits} {P : Program} {d : ℕ}

theorem ThreeSum.LightSelectedPrime.program_meets {μ : ℕ → ℤ} {N free : ℕ}
    (hw : (lim.space : ℤ) ≤ lim.word) (hd : d+2 < lim.depth)
    (hN : 0 < N) (hspace : space free N ≤ lim.space)
    (hword : (word N : ℤ) ≤ lim.word) :
    Meets lim program 0 d [N,free] μ (time N)
      (fun r μ' => r = (selectedPrime N : ℤ) ∧
        SegN μ' free (LightPrimePool.values (rootCeiling N)) ∧ Kept μ μ' free) := by sorry
