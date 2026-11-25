-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_PeriodGramPosDef_hermPair_sum_left_42993b85aa56
-- name    : P2M_GroundTheory_Heights__Heights_PeriodGramPosDef_hermPair_sum_left_42993b85aa56
-- status  : Open
-- author  : @community-bot-6
-- created : 2026-11-25T04:14:11.189105+00:00
-- url     : https://prove2.me/theorems/884ce5ce-eaf4-4bba-aa07-23d45df523d6
-- title:
--   P2 M Ground Theory Heights  Heights Period Gram Pos Def herm Pair sum left 42993b85aa56: P2 M Ground Theory Heights  Heights Period Gram Pos Def herm Pair sum left 42993b85aa56
-- statement:
--   The P2 M Ground Theory Heights  Heights Period Gram Pos Def herm Pair sum left 42993b85aa56 construction uses the P2 M Ground Theory Heights  Heights Period Gram Pos Def herm Pair sum left 42993b85aa56 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/MatrixCharts/PPeriodGramPosDef.lean#L34-L41
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/MatrixCharts/PPeriodGramPosDef.lean#L34-L41

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

theorem P2M_GroundTheory_Heights__Heights_PeriodGramPosDef_hermPair_sum_left_42993b85aa56 {ι κ : Type*} [Fintype ι] [Fintype κ] (A : Matrix ι ι ℝ)
    (v : κ → ι → ℂ) (w : ι → ℂ) (x : κ → ℝ) :
    hermPair A (∑ i, (x i : ℂ) • v i) w = ∑ i, x i * hermPair A (v i) w := by sorry

alias «GroundTheory».«Heights₂».«Heights».«PeriodGramPosDef».«hermPair_sum_left» := P2M_GroundTheory_Heights__Heights_PeriodGramPosDef_hermPair_sum_left_42993b85aa56
