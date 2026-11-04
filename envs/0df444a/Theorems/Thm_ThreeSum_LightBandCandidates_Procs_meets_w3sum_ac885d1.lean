-- Prove2me | Theorems.Thm_ThreeSum_LightBandCandidates_Procs_meets_w3sum_ac885d1
-- name    : ThreeSum.LightBandCandidates.Procs.meets_w3sum_ac885d1
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T12:27:19.815494+00:00
-- url     : https://prove2.me/theorems/acd6ee32-cb84-47de-a9a8-260a896f5f2e
-- title:
--   Procs: meets
-- statement:
--   The Procs construction uses the meets property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/LightBandCandidates.lean#L60-L178
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/LightBandCandidates.lean#L60-L178

import Definitions.Def_Submission_ThreeSum_LightBandCandidatesTable
import Definitions.Def_Submission_ThreeSum_LightBandCandidates
import Definitions.Def_WeightedCache3SUM_Alias_be05f096c8d0157a
import Definitions.Def_WeightedCache3SUM_Alias_887023f6a62327ec
import Definitions.Def_WeightedCache3SUM_Alias_66a9a0be433f5f2b
import Definitions.Def_WeightedCache3SUM_Alias_4c62aff33317338c
import Definitions.Def_WeightedCache3SUM_Alias_d9563e39a04084e5
import Definitions.Def_WeightedCache3SUM_Alias_f2e191e7f7b92ebc
import Definitions.Def_WeightedCache3SUM_Alias_9c326f345c0ba28d
import Definitions.Def_WeightedCache3SUM_Alias_d7235e9f603abd3f
import Definitions.Def_WeightedCache3SUM_Alias_cd0e44d57dc54f82
import Definitions.Def_WeightedCache3SUM_Alias_54cf43efc96d8adf
import Definitions.Def_WeightedCache3SUM_Alias_eb65baeba73fd57c
import Definitions.Def_WeightedCache3SUM_Alias_3b3552e2795ab46d
import Definitions.Def_WeightedCache3SUM_Alias_737c7144994f79de
import Definitions.Def_WeightedCache3SUM_Alias_de0ba8c01a8a208c
import Definitions.Def_WeightedCache3SUM_Alias_d061ef657958844a
import Definitions.Def_WeightedCache3SUM_Alias_aeb4de5e6b301b55
import Theorems.Thm_ThreeSum_LightScaleArray_meets
set_option autoImplicit false
open ThreeSum ThreeSum.LightBandCandidates
open Light BandEnumeration BandCandidateRows
set_option maxHeartbeats 2000000
set_option maxRecDepth 8000
variable {lim : Limits} {P : Program} {d : ℕ} {μ : ℕ → ℤ} {src dst : ℕ}

theorem ThreeSum.LightBandCandidates.Procs.meets_w3sum_ac885d1 {pMain : ℕ} (S : Procs P pMain) (A B C : Family)
    (hw : (lim.space : ℤ) ≤ lim.word) (hd : d + 2 < lim.depth)
    (hsrc : src + LightBandEnumeration.count A.size B.size C.size ≤ dst)
    (hspace : space dst A.size B.size C.size ≤ lim.space) (hword : (word A.size B.size C.size : ℤ) ≤ lim.word)
    (htables : LightBandEnumeration.Tables μ src A B C) :
    Meets lim P pMain d [src, dst, A.size, B.size, C.size] μ (time A.size B.size C.size)
      (fun r ν =>
        r = (LightBandEnumeration.count A.size B.size C.size : ℤ) ∧
          Seg ν dst (cells (records A B C)) ∧
            SameOutside μ ν dst (4 * LightBandEnumeration.count A.size B.size C.size)) := by sorry
