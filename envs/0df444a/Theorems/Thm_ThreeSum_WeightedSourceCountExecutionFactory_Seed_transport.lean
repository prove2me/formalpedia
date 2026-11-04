-- Prove2me | Theorems.Thm_ThreeSum_WeightedSourceCountExecutionFactory_Seed_transport
-- name    : ThreeSum.WeightedSourceCountExecutionFactory.Seed.transport
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T15:11:12.147839+00:00
-- url     : https://prove2.me/theorems/fadecb01-94e1-4c0d-bedd-fa5d36f86283
-- title:
--   Seed: transport
-- statement:
--   The Seed construction uses the transport property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/Weighted/Global/TernarySourceCountWeightSeed.lean#L44-L51
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/Weighted/Global/TernarySourceCountWeightSeed.lean#L44-L51

import Definitions.Def_Submission_Weighted_GlobalBank
import Definitions.Def_Submission_Weighted_SourceCountExecutionFactory
import Definitions.Def_Submission_ThreeSum_TernarySourceWeightSeed
import Definitions.Def_Submission_Weighted_Global_TernarySourceCountWeightSeed
import Theorems.Thm_Light_MatAt_keep
import Theorems.Thm_Light_SegN_keep
import Theorems.Thm_Light_Seg_keep
import Theorems.Thm_Light_VecAt_keep
import Theorems.Thm_ThreeSum_TernarySourceExecutionFactory_Ready_transport
import Theorems.Thm_ThreeSum_TernarySourceExecutionFactory_Seed_transport
import Theorems.Thm_ThreeSum_WeightedCountExecutionFactory_Ready_transport

set_option autoImplicit false
noncomputable section
open ThreeSum ThreeSum.WeightedSourceCountExecutionFactory
open Light TernaryJointType

theorem ThreeSum.WeightedSourceCountExecutionFactory.Seed.transport {N : ℕ} {S : Setup N} {lim : Limits} {d boundary keep : ℕ}
    {μ ν : ℕ→ℤ} {leftWeight rightWeight : ℕ→ℤ}
    (H : Seed S lim d boundary μ leftWeight rightWeight) (hkeep : Kept μ ν keep)
    (I : Immutable S keep) : Seed S lim d boundary ν leftWeight rightWeight := by sorry
