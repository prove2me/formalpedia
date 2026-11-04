-- Prove2me | Theorems.Thm_ThreeSum_LightTernarySignedRow_Procs_meets
-- name    : ThreeSum.LightTernarySignedRow.Procs.meets
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T11:32:49.746388+00:00
-- url     : https://prove2.me/theorems/edeecf7c-46ee-40a8-bab1-1c3148799554
-- title:
--   Procs: meets
-- statement:
--   The Procs construction uses the meets property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/LightTernarySignedRow.lean#L39-L110
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/LightTernarySignedRow.lean#L39-L110

import Definitions.Def_Submission_ThreeSum_LightOutputDecodeDigits
import Definitions.Def_Submission_ThreeSum_LightArray
import Definitions.Def_Submission_ThreeSum_TernarySignedModes
import Definitions.Def_Submission_ThreeSum_LightTernarySignedRow
import Definitions.Def_WeightedCache3SUM_Alias_d7235e9f603abd3f
import Definitions.Def_WeightedCache3SUM_Alias_737c7144994f79de
import Definitions.Def_WeightedCache3SUM_Alias_de0ba8c01a8a208c
import Definitions.Def_WeightedCache3SUM_Alias_54f2bf19dfb01d66
import Definitions.Def_WeightedCache3SUM_Alias_9a4576158068ee52

set_option autoImplicit false
open ThreeSum ThreeSum.LightTernarySignedRow
open Light TernarySignedDigits TernarySignedReduction
set_option maxHeartbeats 1800000
set_option maxRecDepth 7000
variable {lim : Limits} {P : Program} {d : ℕ}

theorem ThreeSum.LightTernarySignedRow.Procs.meets {pMain : ℕ} (S : Procs P pMain)
    {μ : ℕ→ℤ} {J radix dst work V value offset : ℕ} {x sign tag0 tag1 : ℤ}
    (hw : (lim.space : ℤ)≤lim.word) (hd : d+2<lim.depth)
    (hb : 1≤radix) (hval : value≤V) (hshift : x+(offset : ℤ)=(value : ℤ))
    (hx : |x|≤(V : ℤ)) (hoff : offset≤V)
    (hsign : |sign|≤1) (ht0 : |tag0|≤1) (ht1 : |tag1|≤1)
    (hsep : dst+J+2≤work) (hspace : space work V≤lim.space)
    (hword : (word V radix J : ℤ)≤lim.word) :
    Meets lim P pMain d [x,offset,sign,J,radix,dst,work,tag0,tag1] μ (time J V)
      (fun _ ν =>
        (∀ j<J, ν (dst+j)=sign*((OutputDecodeOrder.indices radix J value).getD j 0 : ℤ)) ∧
        ν (dst+J)=tag0 ∧ ν (dst+J+1)=tag1 ∧ Kept μ ν dst) := by sorry
