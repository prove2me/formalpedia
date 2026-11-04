-- Prove2me | Theorems.Thm_ThreeSum_LightColorParameters_meets_w3sum_ac885d1
-- name    : ThreeSum.LightColorParameters.meets_w3sum_ac885d1
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T10:37:56.05663+00:00
-- url     : https://prove2.me/theorems/a621bb68-6528-429a-a3ff-5d69cd8f3a3a
-- title:
--   Light Color Parameters: meets
-- statement:
--   The Light Color Parameters construction uses the meets property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/LightColorParameters.lean#L51-L129
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/LightColorParameters.lean#L51-L129

import Definitions.Def_Submission_ThreeSum_ColorParameters
import Definitions.Def_Submission_ThreeSum_LightSmallDivide
import Definitions.Def_Submission_ThreeSum_LightArray
import Mathlib.Tactic.IntervalCases
import Definitions.Def_Submission_ThreeSum_LightColorParameters
import Definitions.Def_WeightedCache3SUM_Alias_98152438e5b788f3
import Definitions.Def_WeightedCache3SUM_Alias_5d83a00a3f301eb9
import Definitions.Def_WeightedCache3SUM_Alias_de0ba8c01a8a208c
import Definitions.Def_WeightedCache3SUM_Alias_73246870e6a638ab

set_option autoImplicit false
open ThreeSum ThreeSum.LightColorParameters
open Light ColorParameters
set_option maxHeartbeats 1600000
set_option maxRecDepth 9000
variable {lim : Limits} {P : Program} {d W t free : ℕ} {μ : ℕ → ℤ}

theorem ThreeSum.LightColorParameters.meets_w3sum_ac885d1 {pMain pDivide : ℕ} (hp : P[pMain]?=some (body pDivide))
    (hdiv : P[pDivide]?=some LightSmallDivide.body)
    (hw : (lim.space : ℤ) ≤ lim.word) (hspace : free+6 ≤ lim.space)
    (hword : ((t+W+10 : ℕ) : ℤ) ≤ lim.word) (hd : d < lim.depth) :
    Meets lim P pMain d [W,t,free] μ (time t)
      (fun result ν => result=(free : ℤ) ∧ Seg ν free (data W t) ∧ SameOutside μ ν free 6) := by sorry
