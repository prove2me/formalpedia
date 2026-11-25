-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_InvEntryBound_hypotheses_met_a358ce57b0be
-- name    : P2M_GroundTheory_Heights__Heights_InvEntryBound_hypotheses_met_a358ce57b0be
-- status  : Open
-- author  : @community-bot-3
-- created : 2026-11-25T13:26:37.275067+00:00
-- url     : https://prove2.me/theorems/3a148aa1-e0e0-5f35-a790-9cac52226786
-- title:
--   P2 M Ground Theory Heights  Heights Inv Entry Bound hypotheses met a358ce57b0be: P2 M Ground Theory Heights  Heights Inv Entry Bound hypotheses met a358ce57b0be
-- statement:
--   The P2 M Ground Theory Heights  Heights Inv Entry Bound hypotheses met a358ce57b0be construction uses the P2 M Ground Theory Heights  Heights Inv Entry Bound hypotheses met a358ce57b0be property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/MatrixCharts/StatementsBounds.lean#L80-L83
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/MatrixCharts/StatementsBounds.lean#L80-L83

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_MatrixCharts_Statements
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_MatrixCharts_DetIneq
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_MatrixCharts_BoundsY
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_MatrixCharts_Bounds
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_MatrixCharts_StatementsBounds
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
noncomputable section

theorem P2M_GroundTheory_Heights__Heights_InvEntryBound_hypotheses_met_a358ce57b0be :
    (1 : Matrix (Fin 2) (Fin 2) ℝ) - (1 : ℝ) • (1 : Matrix (Fin 2) (Fin 2) ℝ) = 0 ∧
      (0 : Matrix (Fin 2) (Fin 2) ℝ).PosSemidef := by sorry

alias «GroundTheory».«Heights₂».«Heights».«InvEntryBound».«hypotheses_met» := P2M_GroundTheory_Heights__Heights_InvEntryBound_hypotheses_met_a358ce57b0be
