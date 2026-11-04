-- Prove2me | Theorems.Thm_ThreeSum_LightWeightedGlobalArenaTemplate_stores_ends
-- name    : ThreeSum.LightWeightedGlobalArenaTemplate.stores_ends
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T13:52:06.420691+00:00
-- url     : https://prove2.me/theorems/31091131-2a3d-4058-84d5-a7d6c91969ec
-- title:
--   Light Weighted Global Arena Template: stores ends
-- statement:
--   The Light Weighted Global Arena Template construction uses the stores ends property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/Weighted/Global/LightTernaryArenaTemplate.lean#L115-L166
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/Weighted/Global/LightTernaryArenaTemplate.lean#L115-L166

import Definitions.Def_Submission_Weighted_GlobalBank
import Definitions.Def_Submission_Weighted_Global_TernaryArenaLayout
import Definitions.Def_Submission_ThreeSum_LightNatPower
import Definitions.Def_Submission_Weighted_Global_LightTernaryArenaTemplate
import Theorems.Thm_ThreeSum_Karatsuba_CoeffBound_mem
import Theorems.Thm_ThreeSum_LightFiniteTable_stores_ends
import Theorems.Thm_ThreeSum_LightSignedFiniteTable_stores_ends

set_option autoImplicit false
open ThreeSum ThreeSum.LightWeightedGlobalArenaTemplate
open Light WeightedGlobalArenaLayout
set_option maxHeartbeats 6000000
set_option maxRecDepth 20000

theorem ThreeSum.LightWeightedGlobalArenaTemplate.stores_ends {lim : Limits} {P : Program} {depth free C dstSlot : ℕ}
    (fs : List Field) (offset : ℕ) (loc μ : ℕ → ℤ)
    (hfree : loc 1=(free : ℤ)) (hC : loc 24=(C : ℤ)) (hpos : 1≤C)
    (hw : (lim.space : ℤ)≤lim.word) (hend : finish free C≤lim.space)
    (hslot : dstSlot<67) (hspace : addr free C dstSlot+offset+fs.length≤lim.space)
    (hgood : ∀ f∈fs, Good f) (hsquare : |loc 16*loc 16|≤lim.word) :
    Ends lim P depth (stores dstSlot offset fs) ⟨loc,μ⟩ (20*fs.length)
      (fun σ => σ.loc=loc ∧
        Seg σ.mem (addr free C dstSlot+offset) (fs.map (value loc free C)) ∧
        SameOutside μ σ.mem (addr free C dstSlot+offset) fs.length) := by sorry
