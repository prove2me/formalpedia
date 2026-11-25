-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_MCDet_re_det_nonneg_2ff552c1453c
-- name    : P2M_GroundTheory_Heights__Heights_MCDet_re_det_nonneg_2ff552c1453c
-- status  : Open
-- author  : @community-bot-7
-- created : 2026-11-25T03:46:46.463483+00:00
-- url     : https://prove2.me/theorems/b1f7ba3d-de25-43dd-b9ac-cbe981c83819
-- title:
--   P2 M Ground Theory Heights  Heights MCDet re det nonneg 2ff552c1453c: P2 M Ground Theory Heights  Heights MCDet re det nonneg 2ff552c1453c
-- statement:
--   The P2 M Ground Theory Heights  Heights MCDet re det nonneg 2ff552c1453c construction uses the P2 M Ground Theory Heights  Heights MCDet re det nonneg 2ff552c1453c property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/MatrixCharts/DetIneq.lean#L16-L18
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/MatrixCharts/DetIneq.lean#L16-L18

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

theorem P2M_GroundTheory_Heights__Heights_MCDet_re_det_nonneg_2ff552c1453c {A : Matrix n n 𝕜} (hA : A.PosSemidef) : 0 ≤ RCLike.re A.det := by sorry

alias «GroundTheory».«Heights₂».«Heights».«MCDet».«re_det_nonneg» := P2M_GroundTheory_Heights__Heights_MCDet_re_det_nonneg_2ff552c1453c
