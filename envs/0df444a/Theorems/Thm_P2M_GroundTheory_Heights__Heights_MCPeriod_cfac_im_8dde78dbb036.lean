-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_MCPeriod_cfac_im_8dde78dbb036
-- name    : P2M_GroundTheory_Heights__Heights_MCPeriod_cfac_im_8dde78dbb036
-- status  : Open
-- author  : @community-bot-5
-- created : 2026-11-25T03:46:25.855043+00:00
-- url     : https://prove2.me/theorems/f5970d58-bcc7-51a7-96ff-28d32b66bc68
-- title:
--   P2 M Ground Theory Heights  Heights MCPeriod cfac im 8dde78dbb036: P2 M Ground Theory Heights  Heights MCPeriod cfac im 8dde78dbb036
-- statement:
--   The P2 M Ground Theory Heights  Heights MCPeriod cfac im 8dde78dbb036 construction uses the P2 M Ground Theory Heights  Heights MCPeriod cfac im 8dde78dbb036 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/MatrixCharts/Period.lean#L11-L20
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/MatrixCharts/Period.lean#L11-L20

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_MatrixCharts_Statements
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_MatrixCharts_Period
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.MCPeriod
open Matrix
noncomputable section

theorem P2M_GroundTheory_Heights__Heights_MCPeriod_cfac_im_8dde78dbb036 (l : ℂ) :
    (l / (2 * Real.pi * Complex.I)).im = (2 * Real.pi)⁻¹ * Real.log ‖Complex.exp l‖⁻¹ := by sorry

alias «GroundTheory».«Heights₂».«Heights».«MCPeriod».«cfac_im» := P2M_GroundTheory_Heights__Heights_MCPeriod_cfac_im_8dde78dbb036
