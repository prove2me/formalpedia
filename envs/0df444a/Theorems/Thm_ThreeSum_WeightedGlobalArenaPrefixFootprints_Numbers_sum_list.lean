-- Prove2me | Theorems.Thm_ThreeSum_WeightedGlobalArenaPrefixFootprints_Numbers_sum_list
-- name    : ThreeSum.WeightedGlobalArenaPrefixFootprints.Numbers.sum_list
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T20:57:22.982555+00:00
-- url     : https://prove2.me/theorems/55214e0c-50af-4db6-8807-7681bd736fc7
-- title:
--   Numbers: sum list
-- statement:
--   The Numbers construction uses the sum list property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/Weighted/Global/TernaryArenaPrefixFootprints.lean#L214-L215
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/Weighted/Global/TernaryArenaPrefixFootprints.lean#L214-L215

import Definitions.Def_Submission_Weighted_GlobalBank
import Definitions.Def_Submission_Weighted_Global_TernaryArenaPairMass
import Definitions.Def_Submission_Weighted_Global_LightTernaryDimensionsBudget
import Definitions.Def_Submission_ThreeSum_LightTernaryInitialBudgets
import Definitions.Def_Submission_Weighted_Global_TernaryMomentWeightBounds
import Definitions.Def_Submission_Weighted_Global_TernaryArenaCapacity
import Definitions.Def_Submission_ThreeSum_LightTernaryPairedPotential
import Definitions.Def_Submission_Weighted_Global_TernaryMomentChannelResources
import Definitions.Def_Submission_ThreeSum_LightTernaryAppendKeys
import Definitions.Def_Submission_Weighted_Global_TernaryArenaPrefixFootprints
set_option autoImplicit false
noncomputable section
open ThreeSum ThreeSum.WeightedGlobalArenaPrefixFootprints
open WeightedGlobalArenaLayout WeightedGlobalArenaPairMass WeightedGlobalSignedPadding
open WeightedGlobalCoverGoodMaps WeightedGlobalLocalParameters WeightedGlobalNativeCompleteFrontend
set_option maxHeartbeats 6000000
set_option maxRecDepth 20000
attribute [local semireducible] Uniform

theorem ThreeSum.WeightedGlobalArenaPrefixFootprints.Numbers.sum_list (A : Numbers) : A.list.sum=A.localSize+(A.radixCells+(A.joinCells+(A.hits+(A.sourceHistogram+(A.sourceWord+(A.prefixCells+(A.bankCells+(A.nearMetadata+(A.nearDivision+(A.frontendWord+(A.tensorCells+(A.tensorWord+(A.potentialWord+(A.spanCells+(A.originalMatrixCells+(A.menuCells+(A.budgets+(A.depth+(A.reporterWord+(A.reporterCells+(A.candidateScore+(A.prefixHeader+0)))))))))))))))))))))) := by sorry
