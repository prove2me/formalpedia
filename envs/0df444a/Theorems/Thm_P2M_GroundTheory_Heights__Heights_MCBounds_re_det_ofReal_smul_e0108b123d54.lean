-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_MCBounds_re_det_ofReal_smul_e0108b123d54
-- name    : P2M_GroundTheory_Heights__Heights_MCBounds_re_det_ofReal_smul_e0108b123d54
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-24T01:35:23.956926+00:00
-- url     : https://prove2.me/theorems/598e44ea-1c53-460a-a88a-168af5d6ff39
-- title:
--   P2 M Ground Theory Heights  Heights MCBounds re det of Real smul e0108b123d54: P2 M Ground Theory Heights  Heights MCBounds re det of Real smul e0108b123d54
-- statement:
--   The P2 M Ground Theory Heights  Heights MCBounds re det of Real smul e0108b123d54 construction uses the P2 M Ground Theory Heights  Heights MCBounds re det of Real smul e0108b123d54 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/MatrixCharts/PChartBounds.lean#L37-L39
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/MatrixCharts/PChartBounds.lean#L37-L39

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_MatrixCharts_Statements
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_MatrixCharts_DetIneq
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_MatrixCharts_BoundsY
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_MatrixCharts_Bounds
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_MatrixCharts_PChartBounds
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
open Matrix MCBounds
open scoped ComplexOrder
noncomputable section

theorem P2M_GroundTheory_Heights__Heights_MCBounds_re_det_ofReal_smul_e0108b123d54 {k : ℕ} (s : ℝ) (H : Matrix (Fin k) (Fin k) ℂ) :
    ((s : ℂ) • H).det.re = s ^ k * H.det.re := by sorry

alias «GroundTheory».«Heights₂».«Heights».«MCBounds».«re_det_ofReal_smul» := P2M_GroundTheory_Heights__Heights_MCBounds_re_det_ofReal_smul_e0108b123d54
