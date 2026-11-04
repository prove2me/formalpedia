-- Prove2me | Theorems.Thm_ThreeSum_WeightedGlobalTensorWordResources_remaining_guards
-- name    : ThreeSum.WeightedGlobalTensorWordResources.remaining_guards
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T14:42:33.221197+00:00
-- url     : https://prove2.me/theorems/c167f6c0-d8ac-4c4d-bc20-9f968ce44e7f
-- title:
--   Weighted Global Tensor Word Resources: remaining guards
-- statement:
--   The Weighted Global Tensor Word Resources construction uses the remaining guards property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/Weighted/Global/TernaryTensorWordResources.lean#L72-L78
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/Weighted/Global/TernaryTensorWordResources.lean#L72-L78

import Definitions.Def_Submission_Weighted_GlobalBank
import Definitions.Def_Submission_Weighted_Global_LightTernaryTensorFactoryReady
import Definitions.Def_Submission_ThreeSum_PolynomialResources
import Definitions.Def_Submission_Weighted_Global_TernaryTensorWordResources
set_option autoImplicit false
noncomputable section
open ThreeSum ThreeSum.WeightedGlobalTensorWordResources
open LightTernaryPairedPolynomial TernaryPairedColumnEnumeration StageBounds

theorem ThreeSum.WeightedGlobalTensorWordResources.remaining_guards (K J count V sourceU : ℕ) :
    (sourceU+1)^2≤word K J count V sourceU ∧
    J+3≤word K J count V sourceU ∧ count≤word K J count V sourceU ∧
    (J+2)^4≤word K J count V sourceU ∧
    LightWeightRow.word 4 (J+2) ((J+2)^4) 0 1≤word K J count V sourceU := by sorry
