-- Prove2me | Theorems.Thm_ThreeSum_TernaryPhysicalSources_rank_of_type
-- name    : ThreeSum.TernaryPhysicalSources.rank_of_type
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T07:24:03.705504+00:00
-- url     : https://prove2.me/theorems/5c2e038b-5d6b-4943-a5de-689ab693b34d
-- title:
--   Ternary Physical Sources: rank of type
-- statement:
--   The Ternary Physical Sources construction uses the rank of type property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/TernaryPhysicalSources.lean#L29-L34
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/TernaryPhysicalSources.lean#L29-L34

import Definitions.Def_Submission_ThreeSum_TernaryConvolution
import Definitions.Def_Submission_ThreeSum_TernaryPhysicalSources
set_option autoImplicit false
open ThreeSum ThreeSum.TernaryPhysicalSources
open Finset
open ThreeSum.TernaryJointType ThreeSum.TernaryBank ThreeSum.TernaryConvolution

theorem ThreeSum.TernaryPhysicalSources.rank_of_type {N : ℕ} {R : TritWord N} {α : DigitType}
    (h : HasType R α) : rank R=α 1+2*α 2 := by sorry
