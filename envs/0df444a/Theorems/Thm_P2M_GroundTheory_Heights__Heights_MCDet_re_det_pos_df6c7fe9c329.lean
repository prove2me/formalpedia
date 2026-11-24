-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_MCDet_re_det_pos_df6c7fe9c329
-- name    : P2M_GroundTheory_Heights__Heights_MCDet_re_det_pos_df6c7fe9c329
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-24T00:08:20.126245+00:00
-- url     : https://prove2.me/theorems/075edbbf-8d7e-4f39-990e-eb6d6a81319d
-- title:
--   P2 M Ground Theory Heights  Heights MCDet re det pos df6c7fe9c329: P2 M Ground Theory Heights  Heights MCDet re det pos df6c7fe9c329
-- statement:
--   The P2 M Ground Theory Heights  Heights MCDet re det pos df6c7fe9c329 construction uses the P2 M Ground Theory Heights  Heights MCDet re det pos df6c7fe9c329 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/MatrixCharts/DetIneq.lean#L20-L22
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/MatrixCharts/DetIneq.lean#L20-L22

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

theorem P2M_GroundTheory_Heights__Heights_MCDet_re_det_pos_df6c7fe9c329 {A : Matrix n n 𝕜} (hA : A.PosDef) : 0 < RCLike.re A.det := by sorry

alias «GroundTheory».«Heights₂».«Heights».«MCDet».«re_det_pos» := P2M_GroundTheory_Heights__Heights_MCDet_re_det_pos_df6c7fe9c329
