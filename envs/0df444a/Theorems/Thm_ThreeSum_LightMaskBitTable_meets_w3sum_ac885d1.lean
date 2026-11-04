-- Prove2me | Theorems.Thm_ThreeSum_LightMaskBitTable_meets_w3sum_ac885d1
-- name    : ThreeSum.LightMaskBitTable.meets_w3sum_ac885d1
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T10:26:11.039936+00:00
-- url     : https://prove2.me/theorems/2401cade-34d6-4f5f-8a4b-47ba196b882c
-- title:
--   Light Mask Bit Table: meets
-- statement:
--   The Light Mask Bit Table construction uses the meets property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/LightMaskBitTable.lean#L24-L78
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/LightMaskBitTable.lean#L24-L78

import Definitions.Def_Submission_ThreeSum_LightMaskBits
import Definitions.Def_Submission_ThreeSum_LightMaskBitTable
import Definitions.Def_WeightedCache3SUM_Alias_737c7144994f79de
import Definitions.Def_WeightedCache3SUM_Alias_de0ba8c01a8a208c

set_option autoImplicit false
open ThreeSum ThreeSum.LightMaskBitTable
open Light
set_option maxHeartbeats 1000000
variable {lim : Limits} {P : Program} {d : ℕ}

theorem ThreeSum.LightMaskBitTable.meets_w3sum_ac885d1 {pMain pBits pPowers pErase : ℕ}
    (hmain : P[pMain]? = some (body pBits))
    (hbits : P[pBits]? = some (LightMaskBits.body pPowers pErase))
    (hpowers : P[pPowers]? = some powTableBody)
    (herase : P[pErase]? = some (LightMaskErase.body pErase))
    {μ : ℕ → ℤ} {L masks dst n work : ℕ} (mask : ℕ → ℕ)
    (hw : (lim.space : ℤ) ≤ lim.word) (hd : d+L+2 ≤ lim.depth)
    (hspace : work+(L+1) ≤ lim.space)
    (hmasks : masks+n ≤ dst) (hdst : dst+n*L ≤ work)
    (hword : ((2^(L+1) : ℕ) : ℤ) ≤ lim.word)
    (hread : ∀ i < n, μ (masks+i) = (mask i : ℤ))
    (hmaskLt : ∀ i < n, mask i < 2^L) :
    Meets lim P pMain d [L,masks,dst,n,work] μ (time L n)
      (fun _ μ' =>
        (∀ i < n, ∀ a < L, μ' (dst+i*L+a) = (LightMaskBits.bit L (mask i) a : ℤ)) ∧
        KeptBut μ μ' work dst (n*L)) := by sorry
