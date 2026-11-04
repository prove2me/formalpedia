-- Prove2me | Theorems.Thm_ThreeSum_LightZetaPass_program_meets
-- name    : ThreeSum.LightZetaPass.program_meets
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T11:04:43.327283+00:00
-- url     : https://prove2.me/theorems/0f9f71c9-7e5d-46a2-95dd-eef3f53326a0
-- title:
--   Light Zeta Pass: program meets
-- statement:
--   The Light Zeta Pass construction uses the program meets property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/LightZetaPass.lean#L163-L178
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/LightZetaPass.lean#L163-L178

import Definitions.Def_Submission_ThreeSum_LightZetaBatch
import Definitions.Def_Submission_ThreeSum_LightSubsetEnumerationSetup
import Definitions.Def_Submission_ThreeSum_LightZetaPass
import Theorems.Thm_ThreeSum_LightMaskErase_program_meets
import Theorems.Thm_ThreeSum_LightSubsetEnumerationSetup_program_meets
import Theorems.Thm_ThreeSum_LightSubsetEnumeration_program_meets
import Theorems.Thm_ThreeSum_LightSubsetSetup_program_meets
import Theorems.Thm_ThreeSum_LightZetaCell_program_meets

set_option autoImplicit false
open ThreeSum ThreeSum.LightZetaPass
open Light ThreeSum.SubsetAddress ThreeSum.LightZetaCell
open ThreeSum.LightPascal ThreeSum.LightSubsetAddress
variable {lim : Limits} {P : Program}

theorem ThreeSum.LightZetaPass.program_meets {μ : ℕ → ℤ} {L cut src dst maskBase work U d : ℕ}
    (a : Fin L) (f : Finset (Fin L) → ℤ)
    (hw : (lim.space : ℤ) ≤ lim.word) (hcut : cut ≤ L)
    (hsrc : src+downsetCap L cut ≤ maskBase) (hdst : dst+downsetCap L cut ≤ maskBase)
    (hmasks : maskBase+downsetCap L cut ≤ work)
    (hsep : Apart src (downsetCap L cut) dst (downsetCap L cut))
    (hspace : work+tableSize L+(L+1) ≤ lim.space)
    (hword : (((L+1)*2^(L+1) : ℕ) : ℤ) ≤ lim.word)
    (hvalueWord : 2*(U : ℤ) ≤ lim.word)
    (hread : TableAt μ src cut f) (hvalues : ∀ T, T.card ≤ cut → |f T| ≤ U)
    (hd : d+L+6 ≤ lim.depth) :
    Meets lim program 0 d [L,cut,a.val,src,dst,maskBase,work] μ (time L cut)
      (fun _ μ' => TableAt μ' dst cut (Subset.zetaStep a f) ∧
        KeptBut μ μ' maskBase dst (downsetCap L cut)) := by sorry
