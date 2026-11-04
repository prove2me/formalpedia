-- Prove2me | Theorems.Thm_ThreeSum_TernaryPhysicalSources_convolution_histograms
-- name    : ThreeSum.TernaryPhysicalSources.convolution_histograms
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T07:24:10.930921+00:00
-- url     : https://prove2.me/theorems/5ed1c718-9b13-4e52-bd6b-8bf691fe7fa8
-- title:
--   Ternary Physical Sources: convolution histograms
-- statement:
--   The Ternary Physical Sources construction uses the convolution histograms property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/TernaryPhysicalSources.lean#L91-L107
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/TernaryPhysicalSources.lean#L91-L107

import Definitions.Def_Submission_ThreeSum_TernaryConvolution
import Definitions.Def_Submission_ThreeSum_TernaryPhysicalSources
set_option autoImplicit false
open ThreeSum ThreeSum.TernaryPhysicalSources
open Finset
open ThreeSum.TernaryJointType ThreeSum.TernaryBank ThreeSum.TernaryConvolution
variable {ι κ : Type*}

theorem ThreeSum.TernaryPhysicalSources.convolution_histograms {N : ℕ} (S : Finset ι) (T : Finset κ)
    (left : ι → TritWord N) (right : κ → TritWord N) (Q : TritWord N) :
    convolution (histogram S left) (histogram T right) Q=pairCount S T left right Q := by sorry
