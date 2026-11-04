-- Prove2me | Theorems.Thm_ThreeSum_TernaryWeightedPhysicalSources_convolution_histograms
-- name    : ThreeSum.TernaryWeightedPhysicalSources.convolution_histograms
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T08:30:59.141576+00:00
-- url     : https://prove2.me/theorems/ab037f6a-a6cf-48dc-8e48-6bd891d180f1
-- title:
--   Ternary Weighted Physical Sources: convolution histograms
-- statement:
--   The Ternary Weighted Physical Sources construction uses the convolution histograms property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/TernaryWeightedPhysicalSources.lean#L63-L87
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/TernaryWeightedPhysicalSources.lean#L63-L87

import Definitions.Def_Submission_ThreeSum_TernaryPhysicalSources
import Definitions.Def_Submission_ThreeSum_LightTernaryWeightedHistogram
import Definitions.Def_Submission_ThreeSum_TernaryWeightedPhysicalSources
import Theorems.Thm_ThreeSum_TernaryPhysicalSources_convolution_histograms

set_option autoImplicit false
noncomputable section
open ThreeSum ThreeSum.TernaryWeightedPhysicalSources
open Finset TernaryJointType TernaryBank TernaryConvolution
open scoped BigOperators
variable {ι κ : Type*}

theorem ThreeSum.TernaryWeightedPhysicalSources.convolution_histograms {N : ℕ} (S : Finset ι) (T : Finset κ)
    (left : ι → TritWord N) (right : κ → TritWord N)
    (leftWeight : ι → ℤ) (rightWeight : κ → ℤ) (Q : TritWord N) :
    convolution (histogram S left leftWeight) (histogram T right rightWeight) Q=
      pairWeight S T left right leftWeight rightWeight Q := by sorry
