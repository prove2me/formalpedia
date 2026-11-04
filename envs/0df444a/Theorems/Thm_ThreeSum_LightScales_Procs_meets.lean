-- Prove2me | Theorems.Thm_ThreeSum_LightScales_Procs_meets
-- name    : ThreeSum.LightScales.Procs.meets
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T08:16:03.666252+00:00
-- url     : https://prove2.me/theorems/52ea5c2a-afb2-427a-997d-9d5d3c4db46c
-- title:
--   Procs: meets
-- statement:
--   The Procs construction uses the meets property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/LightScales.lean#L189-L195
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/LightScales.lean#L189-L195

import Definitions.Def_Submission_ThreeSum_Scales
import Definitions.Def_Submission_ThreeSum_LightSmallDivide
import Definitions.Def_Submission_ThreeSumApsp_Lang_Lib_Seg
import Definitions.Def_Submission_ThreeSum_LightScales
import Definitions.Def_WeightedCache3SUM_Alias_73246870e6a638ab

set_option autoImplicit false
open ThreeSum ThreeSum.LightScales
open Light ThreeSum.Scales
variable {lim : Limits} {P : Program}

theorem ThreeSum.LightScales.Procs.meets {pMain : ℕ} (S : Procs P pMain)
    {μ : ℕ → ℤ} {n dst d : ℕ}
    (hw : (lim.space : ℤ) ≤ lim.word) (hspace : dst+5 ≤ lim.space)
    (hword : ((1000*(n+1) : ℕ) : ℤ) ≤ lim.word) (hd : d < lim.depth) :
    Meets lim P pMain d [n,dst] μ (time n)
      (fun r μ' => r = (mu n : ℤ) ∧ Seg μ' dst (values n) ∧ SameOutside μ μ' dst 5) := by sorry
