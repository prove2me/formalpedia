-- Prove2me | Theorems.Thm_ThreeSum_TernaryPhysicalSources_rank_eq_type_sum
-- name    : ThreeSum.TernaryPhysicalSources.rank_eq_type_sum
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T07:24:04.044582+00:00
-- url     : https://prove2.me/theorems/140e570f-4a5f-4417-8890-6ab9d5eb8494
-- title:
--   Ternary Physical Sources: rank eq type sum
-- statement:
--   The Ternary Physical Sources construction uses the rank eq type sum property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/TernaryPhysicalSources.lean#L16-L27
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/TernaryPhysicalSources.lean#L16-L27

import Definitions.Def_Submission_ThreeSum_TernaryConvolution
import Definitions.Def_Submission_ThreeSum_TernaryPhysicalSources
set_option autoImplicit false
open ThreeSum ThreeSum.TernaryPhysicalSources
open Finset
open ThreeSum.TernaryJointType ThreeSum.TernaryBank ThreeSum.TernaryConvolution

theorem ThreeSum.TernaryPhysicalSources.rank_eq_type_sum {N : ℕ} (R : TritWord N) :
    rank R = ∑ d : Fin 3, d.val*digitCount R d := by sorry
