-- Prove2me | Theorems.Thm_ThreeSum_LightStageLookup_forced_program_meets
-- name    : ThreeSum.LightStageLookup.forced_program_meets
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T11:03:33.57468+00:00
-- url     : https://prove2.me/theorems/96e40a1b-9a00-4a7e-ba09-533b280de0fe
-- title:
--   Light Stage Lookup: forced program meets
-- statement:
--   The Light Stage Lookup construction uses the forced program meets property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/LightStageLookup.lean#L110-L123
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/LightStageLookup.lean#L110-L123

import Definitions.Def_Submission_ThreeSum_LightZetaStages
import Definitions.Def_Submission_ThreeSum_LightBoxStages
import Definitions.Def_Submission_ThreeSum_LightDownsetAddress
import Definitions.Def_Submission_ThreeSum_LightStageLookup
set_option autoImplicit false
open ThreeSum ThreeSum.LightStageLookup
open Light ThreeSum.SubsetAddress ThreeSum.LightPascal ThreeSum.LightSubsetAddress
variable {lim : Limits} {P : Program}

theorem ThreeSum.LightStageLookup.forced_program_meets {μ : ℕ → ℤ} {L cut base j work d : ℕ}
    (pre tail : Finset (Fin L)) (f : Finset (Fin L) → ℤ)
    (hw : (lim.space : ℤ) ≤ lim.word) (hcut : cut ≤ L)
    (hdata : base+(L+1)*downsetCap L cut ≤ work)
    (hspace : work+tableSize L+(L+1) ≤ lim.space)
    (hword : (((L+1)*2^(L+1) : ℕ) : ℤ) ≤ lim.word)
    (hcard : (pre ∪ tail).card ≤ cut) (hj : j ≤ L)
    (hp : Disjoint pre (SubsetStages.suffix L j)) (ht : tail ⊆ SubsetStages.suffix L j)
    (hstored : LightZetaStages.StoredThrough μ base cut f L) (hd : d+L+5 ≤ lim.depth) :
    Meets lim program 0 d [L,cut,(pre ∪ tail).card,subsetMask (pre ∪ tail),j,base,work] μ (time L)
      (fun r μ' => r = ∑ x ∈ tail.powerset, f (pre ∪ x) ∧ Kept μ μ' work) := by sorry
