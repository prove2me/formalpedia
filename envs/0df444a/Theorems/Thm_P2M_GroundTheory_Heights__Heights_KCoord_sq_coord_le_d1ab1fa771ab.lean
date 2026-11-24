-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_KCoord_sq_coord_le_d1ab1fa771ab
-- name    : P2M_GroundTheory_Heights__Heights_KCoord_sq_coord_le_d1ab1fa771ab
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-24T01:33:13.093801+00:00
-- url     : https://prove2.me/theorems/76d65e95-9d58-455f-981e-af47b3f11e9d
-- title:
--   P2 M Ground Theory Heights  Heights KCoord sq coord le d1ab1fa771ab: P2 M Ground Theory Heights  Heights KCoord sq coord le d1ab1fa771ab
-- statement:
--   The P2 M Ground Theory Heights  Heights KCoord sq coord le d1ab1fa771ab construction uses the P2 M Ground Theory Heights  Heights KCoord sq coord le d1ab1fa771ab property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/HeightKernels/CoordFirst.lean#L11-L53
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/HeightKernels/CoordFirst.lean#L11-L53

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KernelsMatrix
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HeightKernels_CoordFirst
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights
open Matrix
open GroundTheory.Heights₂.Heights.KCoord

theorem P2M_GroundTheory_Heights__Heights_KCoord_sq_coord_le_d1ab1fa771ab {ι : Type*} [Fintype ι] [DecidableEq ι] (Y : Matrix ι ι ℝ) (hY : Y.PosDef)
    (i : ι) (v : ι → ℝ) : v i ^ 2 ≤ Y⁻¹ i i * qf Y v := by sorry

alias «GroundTheory».«Heights₂».«Heights».«KCoord».«sq_coord_le» := P2M_GroundTheory_Heights__Heights_KCoord_sq_coord_le_d1ab1fa771ab
