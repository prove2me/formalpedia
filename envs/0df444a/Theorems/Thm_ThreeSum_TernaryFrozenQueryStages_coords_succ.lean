-- Prove2me | Theorems.Thm_ThreeSum_TernaryFrozenQueryStages_coords_succ
-- name    : ThreeSum.TernaryFrozenQueryStages.coords_succ
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T08:42:30.718287+00:00
-- url     : https://prove2.me/theorems/6cb5e98b-ae40-4b06-8e98-95739d56b430
-- title:
--   Ternary Frozen Query Stages: coords succ
-- statement:
--   The Ternary Frozen Query Stages construction uses the coords succ property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/TernaryFrozenQueryStages.lean#L16-L20
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/TernaryFrozenQueryStages.lean#L16-L20

import Definitions.Def_Submission_ThreeSum_TernaryCodeSemantics
import Definitions.Def_Submission_ThreeSum_TernaryReconstruction
import Definitions.Def_Submission_ThreeSum_TernaryFrozenQueryStages
set_option autoImplicit false
open ThreeSum ThreeSum.TernaryFrozenQueryStages
open ThreeSum.TernaryJointType ThreeSum.TernaryQuery ThreeSum.TernaryReconstruction
set_option maxHeartbeats 2000000

theorem ThreeSum.TernaryFrozenQueryStages.coords_succ {N K : ℕ} (hK : K<N) :
    coords N (K+1)=(⟨K,hK⟩ : Fin N)::coords N K := by sorry
