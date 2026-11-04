-- Prove2me | Theorems.Thm_ThreeSum_WeightedGlobalColoredProgramIdentity_color_eq
-- name    : ThreeSum.WeightedGlobalColoredProgramIdentity.color_eq
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-04T02:14:52.780269+00:00
-- url     : https://prove2.me/theorems/cbb995c9-85a6-4b80-a15a-6dcfb3674777
-- title:
--   Weighted Global Colored Program Identity: color eq
-- statement:
--   The Weighted Global Colored Program Identity construction uses the color eq property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/Weighted/Global/TernaryColoredProgramIdentity.lean#L41-L46
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/Weighted/Global/TernaryColoredProgramIdentity.lean#L41-L46

import Definitions.Def_Submission_Weighted_GlobalBank
import Definitions.Def_Submission_Weighted_Global_TernaryColoredLoopSetup
import Definitions.Def_Submission_Weighted_Global_TernaryColoredPrefixCall
import Definitions.Def_Submission_Weighted_Global_TernaryColoredProgramIdentity
set_option autoImplicit false
noncomputable section
open ThreeSum ThreeSum.WeightedGlobalColoredProgramIdentity
open Light WeightedGlobalConcreteProfile WeightedGlobalArenaSourceSetup
variable {κ : ℕ}

theorem ThreeSum.WeightedGlobalColoredProgramIdentity.color_eq (P : Profile κ) : P.color=libraries P++suffix P := by sorry
