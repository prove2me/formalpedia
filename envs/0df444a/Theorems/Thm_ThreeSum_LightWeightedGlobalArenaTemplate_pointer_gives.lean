-- Prove2me | Theorems.Thm_ThreeSum_LightWeightedGlobalArenaTemplate_pointer_gives
-- name    : ThreeSum.LightWeightedGlobalArenaTemplate.pointer_gives
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T13:49:31.427197+00:00
-- url     : https://prove2.me/theorems/5bef9785-94fd-4eb5-b3ad-ddf16d19b749
-- title:
--   Light Weighted Global Arena Template: pointer gives
-- statement:
--   The Light Weighted Global Arena Template construction uses the pointer gives property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/Weighted/Global/LightTernaryArenaTemplate.lean#L79-L93
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/Weighted/Global/LightTernaryArenaTemplate.lean#L79-L93

import Definitions.Def_Submission_Weighted_GlobalBank
import Definitions.Def_Submission_Weighted_Global_TernaryArenaLayout
import Definitions.Def_Submission_ThreeSum_LightNatPower
import Definitions.Def_Submission_Weighted_Global_LightTernaryArenaTemplate
set_option autoImplicit false
open ThreeSum ThreeSum.LightWeightedGlobalArenaTemplate
open Light WeightedGlobalArenaLayout
set_option maxHeartbeats 6000000
set_option maxRecDepth 20000

theorem ThreeSum.LightWeightedGlobalArenaTemplate.pointer_gives {lim : Limits} {loc : ℕ → ℤ} {free C : ℕ}
    (hfree : loc 1=(free : ℤ)) (hC : loc 24=(C : ℤ)) (hpos : 1≤C)
    (hw : (lim.space : ℤ)≤lim.word) (hend : finish free C≤lim.space)
    (slot : ℕ) (hs : slot<67) (μ : ℕ → ℤ) :
    (ptrExpr slot).Gives lim ⟨loc,μ⟩ (addr free C slot : ℕ) := by sorry
