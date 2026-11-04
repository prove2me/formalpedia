-- Prove2me | Theorems.Thm_ThreeSum_LightTernaryEulerMetadata_rowAddr_ne
-- name    : ThreeSum.LightTernaryEulerMetadata.rowAddr_ne
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T09:30:12.495249+00:00
-- url     : https://prove2.me/theorems/17a17cd7-dee8-4214-9cfd-a10887681ba8
-- title:
--   Light Ternary Euler Metadata: row Addr ne
-- statement:
--   The Light Ternary Euler Metadata construction uses the row Addr ne property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/LightTernaryEulerMetadata.lean#L17-L24
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/LightTernaryEulerMetadata.lean#L17-L24

import Definitions.Def_Submission_ThreeSum_LightTernaryPredecessorTable
import Definitions.Def_Submission_ThreeSum_LightTernaryEulerMetadata
set_option autoImplicit false
open ThreeSum ThreeSum.LightTernaryEulerMetadata
open Light ThreeSum.LightSubsetAddress ThreeSum.LightTernaryPredecessor
set_option maxHeartbeats 3000000
set_option maxRecDepth 10000

theorem ThreeSum.LightTernaryEulerMetadata.rowAddr_ne {ws N i k j l : ℕ} (hi : i<N) (hk : k<N) (hne : i≠k) :
    rowAddr ws N i j≠rowAddr ws N k l := by sorry
