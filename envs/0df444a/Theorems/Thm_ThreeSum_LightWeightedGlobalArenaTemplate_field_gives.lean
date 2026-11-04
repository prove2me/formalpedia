-- Prove2me | Theorems.Thm_ThreeSum_LightWeightedGlobalArenaTemplate_field_gives
-- name    : ThreeSum.LightWeightedGlobalArenaTemplate.field_gives
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T13:49:39.50107+00:00
-- url     : https://prove2.me/theorems/66827022-79ed-4bc6-8489-7871d15bcb57
-- title:
--   Light Weighted Global Arena Template: field gives
-- statement:
--   The Light Weighted Global Arena Template construction uses the field gives property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/Weighted/Global/LightTernaryArenaTemplate.lean#L95-L110
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/Weighted/Global/LightTernaryArenaTemplate.lean#L95-L110

import Definitions.Def_Submission_Weighted_GlobalBank
import Definitions.Def_Submission_Weighted_Global_TernaryArenaLayout
import Definitions.Def_Submission_ThreeSum_LightNatPower
import Definitions.Def_Submission_Weighted_Global_LightTernaryArenaTemplate
set_option autoImplicit false
open ThreeSum ThreeSum.LightWeightedGlobalArenaTemplate
open Light WeightedGlobalArenaLayout
set_option maxHeartbeats 6000000
set_option maxRecDepth 20000

theorem ThreeSum.LightWeightedGlobalArenaTemplate.field_gives {lim : Limits} {loc : ℕ → ℤ} {free C : ℕ}
    (hfree : loc 1=(free : ℤ)) (hC : loc 24=(C : ℤ)) (hpos : 1≤C)
    (hw : (lim.space : ℤ)≤lim.word) (hend : finish free C≤lim.space)
    (hSquare : |loc 16*loc 16|≤lim.word) (f : Field) (hg : Good f) (μ : ℕ → ℤ) :
    (fieldExpr f).Gives lim ⟨loc,μ⟩ (value loc free C f) := by sorry
