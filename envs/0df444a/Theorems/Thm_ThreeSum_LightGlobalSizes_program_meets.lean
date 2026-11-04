-- Prove2me | Theorems.Thm_ThreeSum_LightGlobalSizes_program_meets
-- name    : ThreeSum.LightGlobalSizes.program_meets
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T10:32:31.762678+00:00
-- url     : https://prove2.me/theorems/6601b93b-86ce-4310-a34a-293b406553a4
-- title:
--   Light Global Sizes: program meets
-- statement:
--   The Light Global Sizes construction uses the program meets property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/LightGlobalSizes.lean#L156-L162
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/LightGlobalSizes.lean#L156-L162

import Definitions.Def_Submission_ThreeSum_LightNatPower
import Definitions.Def_Submission_ThreeSum_LightSmallDivide
import Definitions.Def_Submission_ThreeSum_BandScales
import Definitions.Def_Submission_ThreeSumApsp_Lang_Lib_Sqrt
import Definitions.Def_Submission_ThreeSumApsp_Lang_Lib_Seg
import Definitions.Def_Submission_ThreeSum_LightGlobalSizes
import Theorems.Thm_ThreeSum_LightNatPower_program_meets
import Theorems.Thm_ThreeSum_LightSmallDivide_program_meets

set_option autoImplicit false
open ThreeSum ThreeSum.LightGlobalSizes
set_option maxHeartbeats 1000000
open Light LocalCoverBounds
variable {lim : Limits} {P : Program} {d : ℕ}

theorem ThreeSum.LightGlobalSizes.program_meets {μ : ℕ → ℤ} {C p J mu dst : ℕ}
    (hw : (lim.space : ℤ) ≤ lim.word) (hd : d < lim.depth)
    (hC : 1 ≤ C) (hp : 1 ≤ p) (hspace : dst+5 ≤ lim.space)
    (hword : (word C p J mu : ℤ) ≤ lim.word) :
    Meets lim program 0 d [C,p,J,mu,dst] μ (time C J mu)
      (fun r μ' => r = ((p^J : ℕ) : ℤ) ∧ Seg μ' dst (values C p J mu) ∧
        SameOutside μ μ' dst 5) := by sorry
