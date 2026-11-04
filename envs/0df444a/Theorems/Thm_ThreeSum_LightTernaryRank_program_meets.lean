-- Prove2me | Theorems.Thm_ThreeSum_LightTernaryRank_program_meets
-- name    : ThreeSum.LightTernaryRank.program_meets
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T09:46:11.828216+00:00
-- url     : https://prove2.me/theorems/db3d6b35-f17b-44fa-a738-a057ed362bdd
-- title:
--   Light Ternary Rank: program meets
-- statement:
--   The Light Ternary Rank construction uses the program meets property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/LightTernaryRank.lean#L112-L121
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/LightTernaryRank.lean#L112-L121

import Definitions.Def_Submission_ThreeSum_TernaryCodeSemantics
import Definitions.Def_Submission_ThreeSum_LightTernaryRank
import Theorems.Thm_ThreeSum_LightMaskBits_program_meets
import Theorems.Thm_ThreeSum_LightMaskErase_program_meets

set_option autoImplicit false
open ThreeSum ThreeSum.LightTernaryRank
open Light Finset ThreeSum.TernaryJointType ThreeSum.TernaryBank
open ThreeSum.TernaryCodeSemantics ThreeSum.LightSubsetAddress
variable {lim : Limits} {P : Program}

theorem ThreeSum.LightTernaryRank.program_meets {N m powers d : ℕ} (μ : ℕ → ℤ)
    (hw : (lim.space : ℤ) ≤ lim.word)
    (hspace : powers+(2*N+1) ≤ lim.space)
    (hword : ((2^(2*N+1) : ℕ) : ℤ) ≤ lim.word)
    (hscalar : ((2*N+16 : ℕ) : ℤ) ≤ lim.word)
    (hpowers : Powers μ powers (2*N)) (hm : m < 2^(2*N))
    (hdepth : d+2*N+2 ≤ lim.depth) :
    Meets lim program 0 d [N,m,powers] μ (time N)
      (fun r ν => r=(partialRank N m N : ℤ) ∧ ν=μ) := by sorry
