-- Prove2me | Theorems.Thm_ThreeSum_LightSignedCoefficientLayout_meets
-- name    : ThreeSum.LightSignedCoefficientLayout.meets
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T11:37:03.691571+00:00
-- url     : https://prove2.me/theorems/829dcef5-cf35-4115-806b-8dbe51fdddeb
-- title:
--   Light Signed Coefficient Layout: meets
-- statement:
--   The Light Signed Coefficient Layout construction uses the meets property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/LightSignedCoefficientLayout.lean#L19-L81
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/LightSignedCoefficientLayout.lean#L19-L81

import Definitions.Def_Submission_ThreeSum_TernarySignedLayout
import Definitions.Def_Submission_ThreeSum_LightArray
import Definitions.Def_Submission_ThreeSum_LightSignedCoefficientLayout
import Definitions.Def_WeightedCache3SUM_Alias_d7235e9f603abd3f
import Definitions.Def_WeightedCache3SUM_Alias_737c7144994f79de
import Definitions.Def_WeightedCache3SUM_Alias_de0ba8c01a8a208c
import Definitions.Def_WeightedCache3SUM_Alias_54f2bf19dfb01d66
import Definitions.Def_WeightedCache3SUM_Alias_9a4576158068ee52
import Theorems.Thm_ThreeSum_LightTernarySignedRow_Procs_meets

set_option autoImplicit false
open ThreeSum ThreeSum.LightSignedCoefficientLayout
open Light TernarySignedLayout
set_option maxHeartbeats 2000000
variable {lim : Limits} {P : Program} {depth : ℕ}

theorem ThreeSum.LightSignedCoefficientLayout.meets {proc src dst J U : ℕ} (hp : P[proc]?=some body) (μ : ℕ → ℤ) (f : ℕ → ℤ)
    (hw : (lim.space : ℤ)≤lim.word) (hsrc : src+(J+2)≤dst) (hspace : dst+(J+2)≤lim.space)
    (hread : ∀ i < J+2, μ (src+i)=f i) (hf : ∀ i < J+2, |f i|≤(U : ℤ))
    (hword : (U : ℤ)≤lim.word) :
    Meets lim P proc depth [src,dst,J] μ (time J)
      (fun _ ν => (∀ i < J+2, ν (dst+i)=f (offset J i)) ∧ SameOutside μ ν dst (J+2)) := by sorry
