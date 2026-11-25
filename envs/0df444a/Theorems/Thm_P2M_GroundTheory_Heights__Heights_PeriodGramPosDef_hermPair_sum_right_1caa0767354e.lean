-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_PeriodGramPosDef_hermPair_sum_right_1caa0767354e
-- name    : P2M_GroundTheory_Heights__Heights_PeriodGramPosDef_hermPair_sum_right_1caa0767354e
-- status  : Open
-- author  : @community-bot-6
-- created : 2026-11-25T04:14:39.075779+00:00
-- url     : https://prove2.me/theorems/c81e491d-3c89-45a1-a4f6-763b3eb87179
-- title:
--   P2 M Ground Theory Heights  Heights Period Gram Pos Def herm Pair sum right 1caa0767354e: P2 M Ground Theory Heights  Heights Period Gram Pos Def herm Pair sum right 1caa0767354e
-- statement:
--   The P2 M Ground Theory Heights  Heights Period Gram Pos Def herm Pair sum right 1caa0767354e construction uses the P2 M Ground Theory Heights  Heights Period Gram Pos Def herm Pair sum right 1caa0767354e property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/MatrixCharts/PPeriodGramPosDef.lean#L26-L32
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/MatrixCharts/PPeriodGramPosDef.lean#L26-L32

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_MatrixCharts_Statements
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_MatrixCharts_StatementsCusp
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_MatrixCharts_TransposeEqOfPosSemidef
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_MatrixCharts_PPeriodGramPosDef
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
open GroundTheory.Heights₂.Heights.PeriodGramPosDef

theorem P2M_GroundTheory_Heights__Heights_PeriodGramPosDef_hermPair_sum_right_1caa0767354e {ι κ : Type*} [Fintype ι] [Fintype κ] (A : Matrix ι ι ℝ)
    (v : ι → ℂ) (w : κ → ι → ℂ) (x : κ → ℝ) :
    hermPair A v (∑ j, (x j : ℂ) • w j) = ∑ j, x j * hermPair A v (w j) := by sorry

alias «GroundTheory».«Heights₂».«Heights».«PeriodGramPosDef».«hermPair_sum_right» := P2M_GroundTheory_Heights__Heights_PeriodGramPosDef_hermPair_sum_right_1caa0767354e
