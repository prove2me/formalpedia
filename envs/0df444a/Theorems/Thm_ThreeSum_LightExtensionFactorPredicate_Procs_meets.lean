-- Prove2me | Theorems.Thm_ThreeSum_LightExtensionFactorPredicate_Procs_meets
-- name    : ThreeSum.LightExtensionFactorPredicate.Procs.meets
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T10:38:47.859806+00:00
-- url     : https://prove2.me/theorems/39b45112-d123-4b96-821f-2743e5c763e9
-- title:
--   Procs: meets
-- statement:
--   The Procs construction uses the meets property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/LightExtensionFactorPredicate.lean#L61-L131
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/LightExtensionFactorPredicate.lean#L61-L131

import Definitions.Def_Submission_ThreeSum_LightExtensionFactorCheck
import Definitions.Def_Submission_ThreeSum_LightExtensionFactorPredicate
import Theorems.Thm_ThreeSum_LightCoefficientDecode_meets
import Theorems.Thm_ThreeSum_LightExtensionFactorCheck_Procs_meets
import Theorems.Thm_ThreeSum_LightPolynomialCoefficient_meets
import Theorems.Thm_ThreeSum_LightPolynomialProductCheck_meets
import Definitions.Def_WeightedCache3SUM_Alias_e6a24ed55341e959
import Definitions.Def_WeightedCache3SUM_Alias_73246870e6a638ab

set_option autoImplicit false
open ThreeSum ThreeSum.LightExtensionFactorPredicate
open Light
set_option maxHeartbeats 3000000
set_option maxRecDepth 5000
attribute [local instance] ThreeSum.LightExtensionFactorPredicate._p2m_local_instance_595e8f8b6a_7
variable {lim : Limits} {P : Program} {depth : ℕ}

theorem ThreeSum.LightExtensionFactorPredicate.Procs.meets {main ctx u v : ℕ} (S : Procs P main) (C : Layout) (μ : ℕ → ℤ) (f : ℕ → ℕ)
    (hw : (lim.space : ℤ)≤lim.word) (hd : depth+4<lim.depth)
    (hp : 1<C.p) (he : 0<C.degree) (hed : C.degree<C.dim)
    (H : Seg μ ctx (header C)) (hctx : ctx+7≤C.left)
    (hpow : C.powers+(2*C.dim+1)≤C.left)
    (htarget : C.target+2*C.dim≤C.left) (hleft : C.left+2*C.dim≤C.right)
    (hspace : C.right+2*C.dim≤lim.space)
    (hpowRead : ∀ i≤2*C.dim, μ (C.powers+i)=((C.p^i : ℕ) : ℤ))
    (hfRead : ∀ i<2*C.dim, μ (C.target+i)=(f i : ℤ))
    (hword : (word C u v : ℤ)≤lim.word) :
    Meets lim P main depth [u,v,ctx] μ (time C u v)
      (fun z ν => z=result C f u v ∧ Kept μ ν C.left) := by sorry
