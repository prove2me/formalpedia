-- Prove2me | Theorems.Thm_ThreeSum_WeightedGlobalArenaSourceBounds_value_cap
-- name    : ThreeSum.WeightedGlobalArenaSourceBounds.value_cap
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T21:03:46.29868+00:00
-- url     : https://prove2.me/theorems/c8e33de1-86cd-4328-9dad-c5ece8b3107a
-- title:
--   Weighted Global Arena Source Bounds: value cap
-- statement:
--   The Weighted Global Arena Source Bounds construction uses the value cap property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/Weighted/Global/TernaryArenaSourceBounds.lean#L165-L177
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/Weighted/Global/TernaryArenaSourceBounds.lean#L165-L177

import Definitions.Def_Submission_Weighted_GlobalBank
import Definitions.Def_Submission_Weighted_Global_TernaryArenaPrefixFootprints
import Definitions.Def_Submission_Weighted_Global_TernaryArenaSourceBounds
set_option autoImplicit false
noncomputable section
open ThreeSum ThreeSum.WeightedGlobalArenaSourceBounds
open WeightedGlobalArenaPrefixFootprints WeightedGlobalArenaSourceSetup
open WeightedGlobalCoverGoodMaps WeightedGlobalLocalParameters LightTernarySourceHost WeightedGlobalNativeCompleteFrontend
variable {p m F r : ℕ} [Fact p.Prime]

theorem ThreeSum.WeightedGlobalArenaSourceBounds.value_cap (maps : Fin F→Weight m p) (cap : ℕ) (I : Input)
    (n U H : ℕ) (hnB : I.nB≤n) (hnC : I.nC≤n)
    (hweight : I.weightCap≤weight H (4^fixedLength m) U) :
    valueCap (r := r) maps cap I≤(2^fixedAlpha m 2)^r*
      weight H (4^fixedLength m) U*(2*n*(sourceWidth maps cap)^r+1) := by sorry
