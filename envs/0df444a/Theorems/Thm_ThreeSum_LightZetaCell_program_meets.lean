-- Prove2me | Theorems.Thm_ThreeSum_LightZetaCell_program_meets
-- name    : ThreeSum.LightZetaCell.program_meets
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T10:47:10.448257+00:00
-- url     : https://prove2.me/theorems/bf609689-74ae-405b-b4ec-6b84151e4346
-- title:
--   Light Zeta Cell: program meets
-- statement:
--   The Light Zeta Cell construction uses the program meets property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/LightZetaCell.lean#L171-L183
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/LightZetaCell.lean#L171-L183

import Definitions.Def_Submission_ThreeSum_LightMaskErase
import Definitions.Def_Submission_ThreeSum_LightSubsetSetup
import Definitions.Def_Submission_ThreeSum_LightSubsetOffset
import Definitions.Def_Submission_ThreeSum_Subset
import Definitions.Def_Submission_ThreeSum_LightZetaCell
import Theorems.Thm_ThreeSum_LightMaskErase_program_meets
import Theorems.Thm_ThreeSum_LightSubsetSetup_program_meets

set_option autoImplicit false
open ThreeSum ThreeSum.LightZetaCell
open Light ThreeSum.SubsetAddress ThreeSum.MaskErase
open ThreeSum.LightPascal ThreeSum.LightSubsetAddress
variable {lim : Limits} {P : Program}

theorem ThreeSum.LightZetaCell.program_meets {μ : ℕ → ℤ} {L cut src dst work U d : ℕ}
    (S : Finset (Fin L)) (a : Fin L) (f : Finset (Fin L) → ℤ)
    (hw : (lim.space : ℤ) ≤ lim.word)
    (hsrc : src+downsetCap L cut ≤ work) (hdst : dst+downsetCap L cut ≤ work)
    (hspace : work+tableSize L+(L+1) ≤ lim.space)
    (hword : (((L+1)*2^(L+1) : ℕ) : ℤ) ≤ lim.word)
    (hvalueWord : 2*(U : ℤ) ≤ lim.word)
    (hread : TableAt μ src cut f) (hvalues : ∀ T, T.card ≤ cut → |f T| ≤ U)
    (hS : S.card ≤ cut) (hd : d+L+4 ≤ lim.depth) :
    Meets lim program 0 d [L,S.card,subsetMask S,a.val,src,dst,work] μ (time L)
      (fun _ μ' => μ' (dst+subsetRank S) = Subset.zetaStep a f S ∧
        KeptExcept μ μ' work (dst+subsetRank S)) := by sorry
