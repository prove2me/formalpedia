-- Prove2me | Theorems.Thm_ThreeSum_LightStageLookup_box_program_meets
-- name    : ThreeSum.LightStageLookup.box_program_meets
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T11:03:38.465474+00:00
-- url     : https://prove2.me/theorems/1e881c34-c3c3-4b96-9308-133e53adeb5f
-- title:
--   Light Stage Lookup: box program meets
-- statement:
--   The Light Stage Lookup construction uses the box program meets property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/LightStageLookup.lean#L95-L108
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/LightStageLookup.lean#L95-L108

import Definitions.Def_Submission_ThreeSum_LightZetaStages
import Definitions.Def_Submission_ThreeSum_LightBoxStages
import Definitions.Def_Submission_ThreeSum_LightDownsetAddress
import Definitions.Def_Submission_ThreeSum_LightStageLookup
set_option autoImplicit false
open ThreeSum ThreeSum.LightStageLookup
open Light ThreeSum.SubsetAddress ThreeSum.LightPascal ThreeSum.LightSubsetAddress
variable {lim : Limits} {P : Program}

theorem ThreeSum.LightStageLookup.box_program_meets {μ : ℕ → ℤ} {L cut base j work d : ℕ}
    (flags : Finset (Fin L)) (weight : Finset (Fin L) → ℤ)
    (hw : (lim.space : ℤ) ≤ lim.word) (hcut : cut ≤ L)
    (hdata : base+(L+1)*downsetCap L cut ≤ work)
    (hspace : work+tableSize L+(L+1) ≤ lim.space)
    (hword : (((L+1)*2^(L+1) : ℕ) : ℤ) ≤ lim.word)
    (hflags : flags.card ≤ cut) (hj : j ≤ L)
    (hstored : LightBoxStages.StoredThrough μ base cut weight L) (hd : d+L+5 ≤ lim.depth) :
    Meets lim program 0 d [L,cut,flags.card,subsetMask flags,j,base,work] μ (time L)
      (fun r μ' => r = SparseBoxes.boxSum flags (flags ∩ BoxStages.initialCoords L j) weight ∧
        Kept μ μ' work) := by sorry
