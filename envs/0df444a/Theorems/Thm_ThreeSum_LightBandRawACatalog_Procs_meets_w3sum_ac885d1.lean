-- Prove2me | Theorems.Thm_ThreeSum_LightBandRawACatalog_Procs_meets_w3sum_ac885d1
-- name    : ThreeSum.LightBandRawACatalog.Procs.meets_w3sum_ac885d1
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T12:36:51.826546+00:00
-- url     : https://prove2.me/theorems/a7fc4ea0-7302-4421-b86b-32164471f4bc
-- title:
--   Procs: meets
-- statement:
--   The Procs construction uses the meets property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/LightBandRawACatalog.lean#L50-L125
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/LightBandRawACatalog.lean#L50-L125

import Definitions.Def_Submission_ThreeSum_LightBandCandidates
import Definitions.Def_Submission_ThreeSum_LightBandRawA
import Definitions.Def_Submission_ThreeSum_LightHeaderBands
import Definitions.Def_Submission_ThreeSum_LightBandRawACatalog
import Theorems.Thm_Light_SolvesN_meets
import Theorems.Thm_Light_Solves_meets
import Definitions.Def_WeightedCache3SUM_Alias_be05f096c8d0157a
import Definitions.Def_WeightedCache3SUM_Alias_887023f6a62327ec
import Definitions.Def_WeightedCache3SUM_Alias_66a9a0be433f5f2b
import Definitions.Def_WeightedCache3SUM_Alias_f945b0797ad8c830
import Definitions.Def_WeightedCache3SUM_Alias_4c62aff33317338c
import Definitions.Def_WeightedCache3SUM_Alias_d9563e39a04084e5
import Definitions.Def_WeightedCache3SUM_Alias_fecb00c51dea7534
import Definitions.Def_WeightedCache3SUM_Alias_3284ee33b9feff11
import Definitions.Def_WeightedCache3SUM_Alias_09621c124e09fb6e
import Definitions.Def_WeightedCache3SUM_Alias_0eeb60918c21319a
import Definitions.Def_WeightedCache3SUM_Alias_f2e191e7f7b92ebc
import Definitions.Def_WeightedCache3SUM_Alias_9c326f345c0ba28d
import Definitions.Def_WeightedCache3SUM_Alias_d7235e9f603abd3f
import Definitions.Def_WeightedCache3SUM_Alias_cd0e44d57dc54f82
import Definitions.Def_WeightedCache3SUM_Alias_35c8db9f38e66e96
import Definitions.Def_WeightedCache3SUM_Alias_54cf43efc96d8adf
import Definitions.Def_WeightedCache3SUM_Alias_eb65baeba73fd57c
import Definitions.Def_WeightedCache3SUM_Alias_3b3552e2795ab46d
import Definitions.Def_WeightedCache3SUM_Alias_737c7144994f79de
import Definitions.Def_WeightedCache3SUM_Alias_de0ba8c01a8a208c
import Definitions.Def_WeightedCache3SUM_Alias_d061ef657958844a
import Definitions.Def_WeightedCache3SUM_Alias_d98593d0ef804094
import Definitions.Def_WeightedCache3SUM_Alias_aeb4de5e6b301b55
import Theorems.Thm_ThreeSum_LightScaleArray_meets
import Definitions.Def_WeightedCache3SUM_Alias_73246870e6a638ab
import Definitions.Def_WeightedCache3SUM_Alias_f253b70ba796e513
set_option autoImplicit false
open ThreeSum ThreeSum.LightBandRawACatalog
open Light BandEnumeration BandCandidateRows BandRawA
set_option maxHeartbeats 2100000
set_option maxRecDepth 8000
variable {lim : Limits} {P : Program} {d : ℕ} {μ : ℕ → ℤ} {tables rec src headerA headerB headerC nA nB nC g vals : ℕ}
  {f : ℕ → ℤ}

theorem ThreeSum.LightBandRawACatalog.Procs.meets_w3sum_ac885d1 {pMain : ℕ} (S : Procs P pMain) (A B C : Family)
    (hA : A.size = BandPartition.size nA g) (hw : (lim.space : ℤ) ≤ lim.word) (hd : d + 3 < lim.depth) (hg : 0 < g)
    (htable : tables + LightBandEnumeration.count A.size B.size C.size ≤ rec) (hsrc : src + nA ≤ rec)
    (hheadA : headerA + 2 ≤ rec) (hheadB : headerB + 2 ≤ rec) (hheadC : headerC + 2 ≤ rec)
    (hrec : rec + 4 * LightBandEnumeration.count A.size B.size C.size ≤ vals)
    (hspace : space vals A.size B.size C.size g ≤ lim.space) (hword : (word nA A.size B.size C.size g : ℤ) ≤ lim.word)
    (hheaderA : LightHeaderBands.At μ headerA nA A) (hheaderB : LightHeaderBands.At μ headerB nB B)
    (hheaderC : LightHeaderBands.At μ headerC nC C) (htables : LightBandEnumeration.Tables μ tables A B C)
    (hread : ∀ j < nA, μ (src + j) = f j) :
    Meets lim P pMain d [tables, rec, src, headerA, headerB, headerC, g, vals] μ (time A.size B.size C.size g)
      (fun r ν =>
        r = ((items nA g (records A B C)).length : ℤ) ∧
          Seg ν rec (cells (records A B C)) ∧
            Stored ν vals (LightBandRawA.ownerBase vals (LightBandEnumeration.count A.size B.size C.size) g)
                (LightBandRawA.positionBase vals (LightBandEnumeration.count A.size B.size C.size) g) f
                (items nA g (records A B C)) ∧
              Kept μ ν rec) := by sorry
