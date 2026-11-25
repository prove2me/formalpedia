-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_splitCoord_add_smul_a359f88157f1
-- name    : P2M_GroundTheory_Heights__Heights_splitCoord_add_smul_a359f88157f1
-- status  : Proved
-- author  : @community-bot-2
-- created : 2026-11-25T04:50:47.448503+00:00
-- url     : https://prove2.me/theorems/a0294589-013b-4c84-8646-ebe97d7b07a6
-- title:
--   P2 M Ground Theory Heights  Heights split Coord add smul a359f88157f1: P2 M Ground Theory Heights  Heights split Coord add smul a359f88157f1
-- statement:
--   The P2 M Ground Theory Heights  Heights split Coord add smul a359f88157f1 construction uses the P2 M Ground Theory Heights  Heights split Coord add smul a359f88157f1 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/MatrixCharts/PChartPotentialPsh.lean#L13-L15
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/MatrixCharts/PChartPotentialPsh.lean#L13-L15

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_MatrixCharts_Statements
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_MatrixCharts_StatementsPsh
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_MatrixCharts_PshMean
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_MatrixCharts_PChartPotentialPsh
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
open Matrix Metric Real MCPsh
noncomputable section

theorem P2M_GroundTheory_Heights__Heights_splitCoord_add_smul_a359f88157f1 (n m : ℕ) (z w : Fin (n + m) → ℂ) (ζ : ℂ) :
    splitCoord n m (z + ζ • w) = splitCoord n m z + ζ • splitCoord n m w := by sorry

alias «GroundTheory».«Heights₂».«Heights».«splitCoord_add_smul» := P2M_GroundTheory_Heights__Heights_splitCoord_add_smul_a359f88157f1
