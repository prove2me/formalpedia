-- Prove2me | Theorems.Thm_ThreeSum_LightWantedJoin_meets_w3sum_ac885d1
-- name    : ThreeSum.LightWantedJoin.meets_w3sum_ac885d1
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T12:10:33.650679+00:00
-- url     : https://prove2.me/theorems/24aa1537-e008-4672-b047-912a2b291bee
-- title:
--   Light Wanted Join: meets
-- statement:
--   The Light Wanted Join construction uses the meets property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/LightWantedJoin.lean#L45-L136
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/LightWantedJoin.lean#L45-L136

import Definitions.Def_Submission_ThreeSum_LightWantedRow
import Definitions.Def_Submission_ThreeSum_WantedPairs
import Definitions.Def_Submission_ThreeSum_LightWantedJoin
import Definitions.Def_WeightedCache3SUM_Alias_fe1d986d2522f297
import Definitions.Def_WeightedCache3SUM_Alias_9c326f345c0ba28d
import Definitions.Def_WeightedCache3SUM_Alias_d7235e9f603abd3f
import Definitions.Def_WeightedCache3SUM_Alias_cd0e44d57dc54f82
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
import Definitions.Def_WeightedCache3SUM_Alias_aeb4de5e6b301b55
import Definitions.Def_WeightedCache3SUM_Alias_375bd97fc128be02
import Definitions.Def_WeightedCache3SUM_Alias_9b3006da0fcbdf4e
import Theorems.Thm_ThreeSum_LightScaleArray_meets
import Definitions.Def_WeightedCache3SUM_Alias_5471e369d555e9e5
set_option autoImplicit false
open ThreeSum ThreeSum.LightWantedJoin
open Light SourceBuckets WantedPairs
set_option maxHeartbeats 1800000
set_option maxRecDepth 10000
variable {lim : Limits} {P : Program}

theorem ThreeSum.LightWantedJoin.meets_w3sum_ac885d1 {pMain pRow keys offsets flat NR M dst : ℕ}
    (hmain : P[pMain]? = some (body pMain pRow)) (hrow : P[pRow]? = some LightWantedRow.body) (left right : ℕ → ℕ)
    (hright : ∀ j < NR, right j < M) :
    ∀ n d : ℕ,
      ∀ μ : ℕ → ℤ,
        (lim.space : ℤ) ≤ lim.word →
          keys + n ≤ dst →
            offsets + M + 1 ≤ dst →
              flat + NR ≤ dst →
                dst + 2 * count left right NR n ≤ lim.space →
                  d + n + 2 ≤ lim.depth →
                    (∀ i < n, left i < M) →
                      (∀ i < n, μ (keys + i) = (left i : ℤ)) →
                        Stored μ right NR M offsets flat →
                          Meets lim P pMain d [keys, offsets, flat, n, NR, M, dst] μ (time left right NR n)
                            (fun r ν =>
                              r = (count left right NR n : ℤ) ∧
                                Seg ν dst (cells (pairs μ offsets flat left n)) ∧ Kept μ ν dst) := by sorry
