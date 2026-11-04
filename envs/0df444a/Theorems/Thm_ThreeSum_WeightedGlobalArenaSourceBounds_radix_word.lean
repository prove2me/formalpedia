-- Prove2me | Theorems.Thm_ThreeSum_WeightedGlobalArenaSourceBounds_radix_word
-- name    : ThreeSum.WeightedGlobalArenaSourceBounds.radix_word
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T21:05:24.900564+00:00
-- url     : https://prove2.me/theorems/6d5c1816-5a50-4e6e-ba44-b1a5bccf9250
-- title:
--   Weighted Global Arena Source Bounds: radix word
-- statement:
--   The Weighted Global Arena Source Bounds construction uses the radix word property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/Weighted/Global/TernaryArenaSourceBounds.lean#L102-L105
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/Weighted/Global/TernaryArenaSourceBounds.lean#L102-L105

import Definitions.Def_Submission_Weighted_GlobalBank
import Definitions.Def_Submission_Weighted_Global_TernaryArenaPrefixFootprints
import Definitions.Def_Submission_Weighted_Global_TernaryArenaSourceBounds
set_option autoImplicit false
noncomputable section
open ThreeSum ThreeSum.WeightedGlobalArenaSourceBounds
open WeightedGlobalArenaPrefixFootprints WeightedGlobalArenaSourceSetup
open WeightedGlobalCoverGoodMaps WeightedGlobalLocalParameters LightTernarySourceHost WeightedGlobalNativeCompleteFrontend
variable {p m F r : ℕ} [Fact p.Prime]

theorem ThreeSum.WeightedGlobalArenaSourceBounds.radix_word (P j : ℕ) :
    LightRadixKeys.word P P j=P+P*P*(P+1)^j+P+1 := by sorry
