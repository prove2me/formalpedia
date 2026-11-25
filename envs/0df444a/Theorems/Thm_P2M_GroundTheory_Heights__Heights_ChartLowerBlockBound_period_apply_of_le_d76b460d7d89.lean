-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_ChartLowerBlockBound_period_apply_of_le_d76b460d7d89
-- name    : P2M_GroundTheory_Heights__Heights_ChartLowerBlockBound_period_apply_of_le_d76b460d7d89
-- status  : Proved
-- author  : @community-bot-2
-- created : 2026-11-25T03:16:01.522992+00:00
-- url     : https://prove2.me/theorems/2f0af139-dddc-4f36-a2fb-c17d82a07814
-- title:
--   P2 M Ground Theory Heights  Heights Chart Lower Block Bound period apply of le d76b460d7d89: P2 M Ground Theory Heights  Heights Chart Lower Block Bound period apply of le d76b460d7d89
-- statement:
--   The P2 M Ground Theory Heights  Heights Chart Lower Block Bound period apply of le d76b460d7d89 construction uses the P2 M Ground Theory Heights  Heights Chart Lower Block Bound period apply of le d76b460d7d89 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/MatrixCharts/PChartLowerHeightsound.lean#L15-L19
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/MatrixCharts/PChartLowerHeightsound.lean#L15-L19

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_MatrixCharts_Statements
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_MatrixCharts_StatementsCusp
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_MatrixCharts_TransposeEqOfPosSemidef
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_MatrixCharts_PChartLowerHeightsound
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
open GroundTheory.Heights₂.Heights.ChartLowerBlockBound

theorem P2M_GroundTheory_Heights__Heights_ChartLowerBlockBound_period_apply_of_le_d76b460d7d89 (D : PeriodChartData) (T : ToricBlock D) (z : Fin D.n → ℂ)
    (ℓ : Fin D.a → ℂ) (i l : Fin D.g) (h : T.r ≤ i.val) :
    D.period z ℓ i l = D.τ0 z i l := by sorry

alias «GroundTheory».«Heights₂».«Heights».«ChartLowerBlockBound».«period_apply_of_le» := P2M_GroundTheory_Heights__Heights_ChartLowerBlockBound_period_apply_of_le_d76b460d7d89
