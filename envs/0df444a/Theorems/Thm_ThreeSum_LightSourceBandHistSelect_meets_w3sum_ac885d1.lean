-- Prove2me | Theorems.Thm_ThreeSum_LightSourceBandHistSelect_meets_w3sum_ac885d1
-- name    : ThreeSum.LightSourceBandHistSelect.meets_w3sum_ac885d1
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T12:30:20.4807+00:00
-- url     : https://prove2.me/theorems/6782a219-837d-4d25-a90d-67a0c28d82f7
-- title:
--   Light Source Band Hist Select: meets
-- statement:
--   The Light Source Band Hist Select construction uses the meets property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/LightSourceBandHistSelect.lean#L89-L135
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/LightSourceBandHistSelect.lean#L89-L135

import Definitions.Def_Submission_ThreeSum_SourceBandPairSlices
import Definitions.Def_Submission_ThreeSum_LightSourceBandHistSelect
import Theorems.Thm_Light_Ends_next
import Definitions.Def_WeightedCache3SUM_Alias_9c326f345c0ba28d
import Definitions.Def_WeightedCache3SUM_Alias_244efc85702348f3
import Definitions.Def_WeightedCache3SUM_Alias_31257a44f822c74e
import Definitions.Def_WeightedCache3SUM_Alias_de0ba8c01a8a208c
import Definitions.Def_WeightedCache3SUM_Alias_d061ef657958844a
import Definitions.Def_WeightedCache3SUM_Alias_aeb4de5e6b301b55
import Theorems.Thm_ThreeSum_LightScaleArray_meets
import Definitions.Def_WeightedCache3SUM_Alias_8c6e823b5fcef3e6
import Definitions.Def_WeightedCache3SUM_Alias_3b570d79c28763f9
import Definitions.Def_WeightedCache3SUM_Alias_2968a7144f4e39f0
import Definitions.Def_WeightedCache3SUM_Alias_075817043fa4e845
import Theorems.Thm_ThreeSum_LightSourceBuild_Procs_meets
import Definitions.Def_WeightedCache3SUM_Alias_27f79aa230fbddf9
import Definitions.Def_WeightedCache3SUM_Alias_5b14bc7229a63f1e
import Theorems.Thm_ThreeSum_LightSourceResidues_meets
import Definitions.Def_WeightedCache3SUM_Alias_ce5ff1e60c39fd21
import Theorems.Thm_ThreeSum_LightSourceStages_Procs_meets
import Theorems.Thm_ThreeSum_LightSourceStages_ZetaProcs_meets
import Definitions.Def_WeightedCache3SUM_Alias_f29d07b5f5ce2e2c
import Definitions.Def_WeightedCache3SUM_Alias_098d503c7eb426c7
import Definitions.Def_WeightedCache3SUM_Alias_037fdff845f4735d
import Definitions.Def_WeightedCache3SUM_Alias_8a94481881de516b
import Definitions.Def_WeightedCache3SUM_Alias_c0e528b1e0cee255
import Definitions.Def_WeightedCache3SUM_Alias_44f02ed11cdb23f7
import Definitions.Def_WeightedCache3SUM_Alias_d110f06b53aa1a96
import Definitions.Def_WeightedCache3SUM_Alias_197272b1cee37ac5

set_option autoImplicit false
open ThreeSum ThreeSum.LightSourceBandHistSelect
open Light BandPartition SourceBandPairData SourceBandPairSlices
set_option maxHeartbeats 2500000
set_option maxRecDepth 12000
variable {lim : Limits} {P : Program} {d : ℕ}

theorem ThreeSum.LightSourceBandHistSelect.meets_w3sum_ac885d1 {pMain : ℕ} (hmain : P[pMain]?=some body)
    {μ : ℕ → ℤ} {fL fR : ℕ → ℤ} {pair NL NR g p m i dst : ℕ} {shift : ℤ}
    (H : Stored μ fL fR pair NL NR g p m shift)
    (hw : (lim.space : ℤ) ≤ lim.word) (hm : 0 < m)
    (hb : next pair NL NR g m ≤ dst) (hs : dst+2 ≤ lim.space)
    (hwN : ((NL+NR+i+6 : ℕ) : ℤ) ≤ lim.word) :
    Meets lim P pMain d [pair,i,dst] μ 400
      (fun _ ν => ν dst=(histLeft pair NL NR g m i : ℤ) ∧
        ν (dst+1)=(histRight pair NL NR g m i : ℤ) ∧ Kept μ ν dst) := by sorry
