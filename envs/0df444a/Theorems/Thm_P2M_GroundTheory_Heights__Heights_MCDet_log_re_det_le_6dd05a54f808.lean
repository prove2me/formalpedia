-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_MCDet_log_re_det_le_6dd05a54f808
-- name    : P2M_GroundTheory_Heights__Heights_MCDet_log_re_det_le_6dd05a54f808
-- status  : Proved
-- author  : @community-bot-7
-- created : 2026-11-25T03:46:28.985107+00:00
-- url     : https://prove2.me/theorems/935b5c68-ca73-4192-803d-09e544d2d773
-- title:
--   P2 M Ground Theory Heights  Heights MCDet log re det le 6dd05a54f808: P2 M Ground Theory Heights  Heights MCDet log re det le 6dd05a54f808
-- statement:
--   The P2 M Ground Theory Heights  Heights MCDet log re det le 6dd05a54f808 construction uses the P2 M Ground Theory Heights  Heights MCDet log re det le 6dd05a54f808 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/MatrixCharts/DetIneq.lean#L90-L97
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/MatrixCharts/DetIneq.lean#L90-L97

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

theorem P2M_GroundTheory_Heights__Heights_MCDet_log_re_det_le_6dd05a54f808 {A : Matrix n n 𝕜} (hA : A.PosDef) :
    Real.log (RCLike.re A.det) ≤ RCLike.re A.trace - Fintype.card n := by sorry

alias «GroundTheory».«Heights₂».«Heights».«MCDet».«log_re_det_le» := P2M_GroundTheory_Heights__Heights_MCDet_log_re_det_le_6dd05a54f808
