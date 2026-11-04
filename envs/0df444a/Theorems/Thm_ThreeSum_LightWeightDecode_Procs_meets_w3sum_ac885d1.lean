-- Prove2me | Theorems.Thm_ThreeSum_LightWeightDecode_Procs_meets_w3sum_ac885d1
-- name    : ThreeSum.LightWeightDecode.Procs.meets_w3sum_ac885d1
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T10:23:31.869403+00:00
-- url     : https://prove2.me/theorems/e8bb0048-030c-422b-ae5a-d8872a3bcff3
-- title:
--   Procs: meets
-- statement:
--   The Procs construction uses the meets property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/LightWeightDecode.lean#L43-L108
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/LightWeightDecode.lean#L43-L108

import Definitions.Def_Submission_ThreeSum_LightWeightRow
import Definitions.Def_Submission_ThreeSum_LightWeightDecode
import Definitions.Def_WeightedCache3SUM_Alias_e6a24ed55341e959
import Definitions.Def_WeightedCache3SUM_Alias_73246870e6a638ab
import Definitions.Def_WeightedCache3SUM_Alias_b5410f4bcc10d599

set_option autoImplicit false
open ThreeSum ThreeSum.LightWeightDecode
open Light
variable {lim : Limits} {P : Program} {d : ℕ}

theorem ThreeSum.LightWeightDecode.Procs.meets_w3sum_ac885d1 {pMain : ℕ} (S : Procs P pMain)
    {μ : ℕ → ℤ} {L p k dst work : ℕ}
    (hw : (lim.space : ℤ) ≤ lim.word) (hd : d+2 < lim.depth) (hp : 1 ≤ p)
    (hdst : dst+2*L ≤ work) (hspace : work+(2*L+1) ≤ lim.space)
    (hword : (word L p k : ℤ) ≤ lim.word) :
    Meets lim P pMain d [L,p,k,dst,work] μ (time L k)
      (fun _ μ' => Rows μ' dst L p k ∧
        (∀ e ≤ 2*L, μ' (work+e) = ((p^e : ℕ) : ℤ)) ∧
        KeptBut μ μ' work dst (2*L)) := by sorry
