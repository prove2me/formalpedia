-- Prove2me | Theorems.Thm_ThreeSum_LightExtensionFactorCheck_Procs_meets
-- name    : ThreeSum.LightExtensionFactorCheck.Procs.meets
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T10:30:12.326372+00:00
-- url     : https://prove2.me/theorems/a67f9389-cd10-48a9-b579-b944b5dcd4a9
-- title:
--   Procs: meets
-- statement:
--   The Procs construction uses the meets property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/LightExtensionFactorCheck.lean#L42-L102
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/LightExtensionFactorCheck.lean#L42-L102

import Definitions.Def_Submission_ThreeSum_LightPolynomialProductCheck
import Definitions.Def_Submission_ThreeSum_LightCoefficientDecode
import Definitions.Def_Submission_ThreeSum_LightExtensionFactorCheck
import Theorems.Thm_ThreeSum_LightCoefficientDecode_meets
import Theorems.Thm_ThreeSum_LightPolynomialCoefficient_meets
import Theorems.Thm_ThreeSum_LightPolynomialProductCheck_meets
import Definitions.Def_WeightedCache3SUM_Alias_e6a24ed55341e959
import Definitions.Def_WeightedCache3SUM_Alias_73246870e6a638ab

set_option autoImplicit false
open ThreeSum ThreeSum.LightExtensionFactorCheck
open Light
set_option maxHeartbeats 2000000
variable {lim : Limits} {P : Program} {depth : ℕ}

theorem ThreeSum.LightExtensionFactorCheck.Procs.meets {main d e p u v powers target hBase gBase : ℕ}
    (S : Procs P main) (μ : ℕ → ℤ) (f : ℕ → ℕ)
    (hw : (lim.space : ℤ)≤lim.word) (hd : depth+3<lim.depth)
    (hp : 1<p) (he : 0<e) (hed : e<d)
    (hpow : powers+(2*d+1)≤hBase) (htarget : target+2*d≤hBase)
    (hh : hBase+2*d≤gBase) (hspace : gBase+2*d≤lim.space)
    (hpowRead : ∀ i≤2*d, μ (powers+i)=((p^i : ℕ) : ℤ))
    (hfRead : ∀ i<2*d, μ (target+i)=(f i : ℤ))
    (hword : (word d e p u v : ℤ)≤lim.word) :
    Meets lim P main depth [u,v,p,d,e,powers,target,hBase,gBase] μ (time d e p u v)
      (fun z ν => z=LightPolynomialProductCheck.flag p (digits p u) (digits p v) f
          (e+1) (d-e+1) (2*d) ∧ Kept μ ν hBase) := by sorry
