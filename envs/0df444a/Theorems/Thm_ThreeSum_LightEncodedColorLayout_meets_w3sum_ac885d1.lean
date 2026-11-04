-- Prove2me | Theorems.Thm_ThreeSum_LightEncodedColorLayout_meets_w3sum_ac885d1
-- name    : ThreeSum.LightEncodedColorLayout.meets_w3sum_ac885d1
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T13:01:29.11224+00:00
-- url     : https://prove2.me/theorems/615d01ef-0934-4fa7-9eb1-fd74199a1882
-- title:
--   Light Encoded Color Layout: meets
-- statement:
--   The Light Encoded Color Layout construction uses the meets property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/LightEncodedColorLayout.lean#L62-L137
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/LightEncodedColorLayout.lean#L62-L137

import Definitions.Def_Submission_ThreeSum_EncodedColorLayout
import Definitions.Def_Submission_ThreeSum_LightEncodedColorLayout
import Theorems.Thm_Light_SolvesN_meets
import Theorems.Thm_Light_Solves_meets
import Definitions.Def_WeightedCache3SUM_Alias_be05f096c8d0157a
import Definitions.Def_WeightedCache3SUM_Alias_887023f6a62327ec
import Definitions.Def_WeightedCache3SUM_Alias_66a9a0be433f5f2b
import Definitions.Def_WeightedCache3SUM_Alias_f945b0797ad8c830
import Definitions.Def_WeightedCache3SUM_Alias_4c62aff33317338c
import Definitions.Def_WeightedCache3SUM_Alias_d9563e39a04084e5
import Definitions.Def_WeightedCache3SUM_Alias_fecb00c51dea7534
import Definitions.Def_WeightedCache3SUM_Alias_ee0aafec5c99c3fa
import Definitions.Def_WeightedCache3SUM_Alias_984b86210e82afdf
import Definitions.Def_WeightedCache3SUM_Alias_1109447aa6c56181
import Definitions.Def_WeightedCache3SUM_Alias_4321abdf54a97fe0
import Definitions.Def_WeightedCache3SUM_Alias_3284ee33b9feff11
import Definitions.Def_WeightedCache3SUM_Alias_09621c124e09fb6e
import Definitions.Def_WeightedCache3SUM_Alias_0eeb60918c21319a
import Definitions.Def_WeightedCache3SUM_Alias_f2e191e7f7b92ebc
import Definitions.Def_WeightedCache3SUM_Alias_9ba359ecf22e73cc
import Definitions.Def_WeightedCache3SUM_Alias_0f0d845b38fcc358
import Definitions.Def_WeightedCache3SUM_Alias_9c326f345c0ba28d
import Definitions.Def_WeightedCache3SUM_Alias_d7235e9f603abd3f
import Definitions.Def_WeightedCache3SUM_Alias_cd0e44d57dc54f82
import Definitions.Def_WeightedCache3SUM_Alias_98152438e5b788f3
import Definitions.Def_WeightedCache3SUM_Alias_ec1db2019105351a
import Definitions.Def_WeightedCache3SUM_Alias_e24e346b903ae22f
import Definitions.Def_WeightedCache3SUM_Alias_1bc522b5c56beb35
import Definitions.Def_WeightedCache3SUM_Alias_5d83a00a3f301eb9
import Definitions.Def_WeightedCache3SUM_Alias_35c8db9f38e66e96
import Definitions.Def_WeightedCache3SUM_Alias_54cf43efc96d8adf
import Definitions.Def_WeightedCache3SUM_Alias_eb65baeba73fd57c
import Definitions.Def_WeightedCache3SUM_Alias_3b3552e2795ab46d
import Definitions.Def_WeightedCache3SUM_Alias_3252ff1ef14149f2
import Definitions.Def_WeightedCache3SUM_Alias_737c7144994f79de
import Definitions.Def_WeightedCache3SUM_Alias_de0ba8c01a8a208c
import Definitions.Def_WeightedCache3SUM_Alias_d061ef657958844a
import Definitions.Def_WeightedCache3SUM_Alias_e1d95931a2ead3e4
import Theorems.Thm_ThreeSum_LightModuloCounts_Procs_meets
import Definitions.Def_WeightedCache3SUM_Alias_03cdb09d18890d4e
import Definitions.Def_WeightedCache3SUM_Alias_d98593d0ef804094
import Definitions.Def_WeightedCache3SUM_Alias_aeb4de5e6b301b55
import Theorems.Thm_ThreeSum_LightPrimality_Procs_meets
import Definitions.Def_WeightedCache3SUM_Alias_137b880911028d95
import Theorems.Thm_ThreeSum_LightPrimeChain_Procs_meets
import Theorems.Thm_ThreeSum_LightPrimeMinimum_Procs_meets
import Definitions.Def_WeightedCache3SUM_Alias_a00dee90c4e0ea45
import Definitions.Def_WeightedCache3SUM_Alias_9b3006da0fcbdf4e
import Theorems.Thm_ThreeSum_LightScaleArray_meets
import Definitions.Def_WeightedCache3SUM_Alias_73246870e6a638ab
import Definitions.Def_WeightedCache3SUM_Alias_f253b70ba796e513
import Definitions.Def_WeightedCache3SUM_Alias_280261ae8ac7fab5
import Theorems.Thm_ThreeSum_ReportingHostRelocation_meets

set_option autoImplicit false
open ThreeSum ThreeSum.LightEncodedColorLayout
open Light BandPartition EncodedColorLayout
set_option maxHeartbeats 2200000
set_option maxRecDepth 11000
variable {lim : Limits} {P : Program} {d : ℕ}

theorem ThreeSum.LightEncodedColorLayout.meets_w3sum_ac885d1 {pMain pDivide n g free : ℕ} {μ : ℕ → ℤ}
    (hmain : P[pMain]?=some (body pDivide)) (hdiv : P[pDivide]?=some LightSmallDivide.body)
    (hw : (lim.space : ℤ) ≤ lim.word) (hn : 0 < n) (hg : 0 < g)
    (hspace : normalizedEnd free n g+1 ≤ lim.space)
    (hword : (word n g : ℤ) ≤ lim.word) (hd : d < lim.depth) :
    Meets lim P pMain d [n,g,free] μ (time n g)
      (fun r ν => r=(normalizedEnd free n g : ℤ) ∧ Seg ν free (normalizedHeads free n g) ∧ Kept μ ν free) := by sorry
