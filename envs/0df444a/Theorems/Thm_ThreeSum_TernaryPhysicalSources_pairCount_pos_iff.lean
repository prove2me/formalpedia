-- Prove2me | Theorems.Thm_ThreeSum_TernaryPhysicalSources_pairCount_pos_iff
-- name    : ThreeSum.TernaryPhysicalSources.pairCount_pos_iff
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T07:24:15.283487+00:00
-- url     : https://prove2.me/theorems/799f060c-60bd-4788-acdf-6eda0a4878cd
-- title:
--   Ternary Physical Sources: pair Count pos iff
-- statement:
--   The Ternary Physical Sources construction uses the pair Count pos iff property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/TernaryPhysicalSources.lean#L109-L131
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/TernaryPhysicalSources.lean#L109-L131

import Definitions.Def_Submission_ThreeSum_TernaryConvolution
import Definitions.Def_Submission_ThreeSum_TernaryPhysicalSources
set_option autoImplicit false
open ThreeSum ThreeSum.TernaryPhysicalSources
open Finset
open ThreeSum.TernaryJointType ThreeSum.TernaryBank ThreeSum.TernaryConvolution
variable {ι κ : Type*}

theorem ThreeSum.TernaryPhysicalSources.pairCount_pos_iff {N : ℕ} (S : Finset ι) (T : Finset κ)
    (left : ι → TritWord N) (right : κ → TritWord N) (Q : TritWord N) :
    0 < pairCount S T left right Q ↔
      ∃ i ∈ S, ∃ j ∈ T, Adds (left i) (right j) Q := by sorry
