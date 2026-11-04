-- Prove2me | Theorems.Thm_ThreeSum_LightBandCandidatesRow_meets_w3sum_ac885d1
-- name    : ThreeSum.LightBandCandidatesRow.meets_w3sum_ac885d1
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T12:01:22.980966+00:00
-- url     : https://prove2.me/theorems/99217880-f6e6-4b3a-a5c5-58aba8ff0f99
-- title:
--   Light Band Candidates Row: meets
-- statement:
--   The Light Band Candidates Row construction uses the meets property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/LightBandCandidatesRow.lean#L29-L76
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/LightBandCandidatesRow.lean#L29-L76

import Definitions.Def_Submission_ThreeSum_LightBandCandidatesCell
import Definitions.Def_Submission_ThreeSum_LightBandCandidatesRow
import Definitions.Def_WeightedCache3SUM_Alias_be05f096c8d0157a
import Definitions.Def_WeightedCache3SUM_Alias_4c62aff33317338c
import Definitions.Def_WeightedCache3SUM_Alias_d9563e39a04084e5
import Definitions.Def_WeightedCache3SUM_Alias_f2e191e7f7b92ebc
import Definitions.Def_WeightedCache3SUM_Alias_d7235e9f603abd3f
import Definitions.Def_WeightedCache3SUM_Alias_cd0e44d57dc54f82
import Definitions.Def_WeightedCache3SUM_Alias_54cf43efc96d8adf
import Definitions.Def_WeightedCache3SUM_Alias_737c7144994f79de
import Definitions.Def_WeightedCache3SUM_Alias_de0ba8c01a8a208c

set_option autoImplicit false
open ThreeSum ThreeSum.LightBandCandidatesRow
open Light BandCandidateRows
set_option maxHeartbeats 1600000
set_option maxRecDepth 7000
variable {lim : Limits} {P : Program} {d : ℕ} {μ : ℕ → ℤ}
    {src dst n outer U : ℕ} {f : ℕ → ℕ}

theorem ThreeSum.LightBandCandidatesRow.meets_w3sum_ac885d1 {pMain pCell : ℕ} (mode : Mode)
    (hmain : P[pMain]?=some (body pCell))
    (hcell : P[pCell]?=some (LightBandCandidatesCell.body mode))
    (hw : (lim.space : ℤ) ≤ lim.word) (hd : d < lim.depth)
    (hsrc : src+n ≤ dst) (hspace : dst+4*n ≤ lim.space)
    (hword : ((U+10 : ℕ) : ℤ) ≤ lim.word)
    (hn : n ≤ U) (houter : outer ≤ U)
    (hf : ∀ j < n, f j ≤ U) (hread : ∀ j < n, μ (src+j)=(f j : ℤ)) :
    Meets lim P pMain d [src,dst,n,outer] μ (time n)
      (fun _ ν =>
        (∀ j < n, Seg ν (dst+4*j) (make mode outer j (f j)).cells) ∧
        SameOutside μ ν dst (4*n)) := by sorry
