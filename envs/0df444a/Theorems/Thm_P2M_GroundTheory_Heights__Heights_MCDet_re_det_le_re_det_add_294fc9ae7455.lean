-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_MCDet_re_det_le_re_det_add_294fc9ae7455
-- name    : P2M_GroundTheory_Heights__Heights_MCDet_re_det_le_re_det_add_294fc9ae7455
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-23T21:11:32.303298+00:00
-- url     : https://prove2.me/theorems/3455188d-66d3-4970-a92a-5a7e0e8facac
-- title:
--   P2 M Ground Theory Heights  Heights MCDet re det le re det add 294fc9ae7455: P2 M Ground Theory Heights  Heights MCDet re det le re det add 294fc9ae7455
-- statement:
--   The P2 M Ground Theory Heights  Heights MCDet re det le re det add 294fc9ae7455 construction uses the P2 M Ground Theory Heights  Heights MCDet re det le re det add 294fc9ae7455 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/MatrixCharts/DetIneq.lean#L47-L83
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/MatrixCharts/DetIneq.lean#L47-L83

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_MatrixCharts_Statements
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_MatrixCharts_DetIneq
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.MCDet
open Matrix
open scoped MatrixOrder ComplexOrder
variable {𝕜 : Type*} [RCLike 𝕜] {n m : Type*} [Fintype n] [DecidableEq n] [Fintype m]

theorem P2M_GroundTheory_Heights__Heights_MCDet_re_det_le_re_det_add_294fc9ae7455 {A P : Matrix n n 𝕜} (hA : A.PosSemidef) (hP : P.PosSemidef) :
    RCLike.re A.det ≤ RCLike.re (A + P).det := by sorry

alias «GroundTheory».«Heights₂».«Heights».«MCDet».«re_det_le_re_det_add» := P2M_GroundTheory_Heights__Heights_MCDet_re_det_le_re_det_add_294fc9ae7455
