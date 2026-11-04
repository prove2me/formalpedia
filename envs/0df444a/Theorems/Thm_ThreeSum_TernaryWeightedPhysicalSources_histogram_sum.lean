-- Prove2me | Theorems.Thm_ThreeSum_TernaryWeightedPhysicalSources_histogram_sum
-- name    : ThreeSum.TernaryWeightedPhysicalSources.histogram_sum
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T09:20:10.873044+00:00
-- url     : https://prove2.me/theorems/8fe894c2-2d61-4841-afdd-f5d78c56c17a
-- title:
--   Ternary Weighted Physical Sources: histogram sum
-- statement:
--   The Ternary Weighted Physical Sources construction uses the histogram sum property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/TernaryWeightedPhysicalSources.lean#L46-L55
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/TernaryWeightedPhysicalSources.lean#L46-L55

import Definitions.Def_Submission_ThreeSum_TernaryPhysicalSources
import Definitions.Def_Submission_ThreeSum_LightTernaryWeightedHistogram
import Definitions.Def_Submission_ThreeSum_TernaryWeightedPhysicalSources
import Theorems.Thm_ThreeSum_TernaryPhysicalSources_histogram_sum

set_option autoImplicit false
noncomputable section
open ThreeSum ThreeSum.TernaryWeightedPhysicalSources
open Finset TernaryJointType TernaryBank TernaryConvolution
open scoped BigOperators
variable {ι κ : Type*}

theorem ThreeSum.TernaryWeightedPhysicalSources.histogram_sum {N : ℕ} (S : Finset ι) (word : ι → TritWord N)
    (weight : ι → ℤ) (F : TritWord N → ℤ) :
    (∑ A, histogram S word weight A*F A)=∑ i ∈ S, weight i*F (word i) := by sorry
