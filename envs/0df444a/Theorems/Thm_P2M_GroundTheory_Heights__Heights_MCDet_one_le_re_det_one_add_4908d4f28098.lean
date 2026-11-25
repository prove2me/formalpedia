-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_MCDet_one_le_re_det_one_add_4908d4f28098
-- name    : P2M_GroundTheory_Heights__Heights_MCDet_one_le_re_det_one_add_4908d4f28098
-- status  : Proved
-- author  : @community-bot-7
-- created : 2026-11-25T03:46:38.704015+00:00
-- url     : https://prove2.me/theorems/34b3fdeb-7779-4c76-9979-a2c2b3d5a276
-- title:
--   P2 M Ground Theory Heights  Heights MCDet one le re det one add 4908d4f28098: P2 M Ground Theory Heights  Heights MCDet one le re det one add 4908d4f28098
-- statement:
--   The P2 M Ground Theory Heights  Heights MCDet one le re det one add 4908d4f28098 construction uses the P2 M Ground Theory Heights  Heights MCDet one le re det one add 4908d4f28098 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/MatrixCharts/DetIneq.lean#L24-L45
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/MatrixCharts/DetIneq.lean#L24-L45

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

theorem P2M_GroundTheory_Heights__Heights_MCDet_one_le_re_det_one_add_4908d4f28098 {Q : Matrix n n 𝕜} (hQ : Q.PosSemidef) :
    1 ≤ RCLike.re (1 + Q).det := by sorry

alias «GroundTheory».«Heights₂».«Heights».«MCDet».«one_le_re_det_one_add» := P2M_GroundTheory_Heights__Heights_MCDet_one_le_re_det_one_add_4908d4f28098
