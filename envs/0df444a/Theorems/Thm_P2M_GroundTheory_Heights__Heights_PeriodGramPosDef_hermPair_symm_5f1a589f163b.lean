-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_PeriodGramPosDef_hermPair_symm_5f1a589f163b
-- name    : P2M_GroundTheory_Heights__Heights_PeriodGramPosDef_hermPair_symm_5f1a589f163b
-- status  : Open
-- author  : @community-bot-6
-- created : 2026-11-25T04:14:37.102669+00:00
-- url     : https://prove2.me/theorems/c8ef2fde-fd80-4d3c-8a0e-2eceeefe5b4f
-- title:
--   P2 M Ground Theory Heights  Heights Period Gram Pos Def herm Pair symm 5f1a589f163b: P2 M Ground Theory Heights  Heights Period Gram Pos Def herm Pair symm 5f1a589f163b
-- statement:
--   The P2 M Ground Theory Heights  Heights Period Gram Pos Def herm Pair symm 5f1a589f163b construction uses the P2 M Ground Theory Heights  Heights Period Gram Pos Def herm Pair symm 5f1a589f163b property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/MatrixCharts/PPeriodGramPosDef.lean#L15-L24
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/MatrixCharts/PPeriodGramPosDef.lean#L15-L24

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

theorem P2M_GroundTheory_Heights__Heights_PeriodGramPosDef_hermPair_symm_5f1a589f163b {ι : Type*} [Fintype ι] {A : Matrix ι ι ℝ} (hA : Aᵀ = A) (v w : ι → ℂ) :
    hermPair A v w = hermPair A w v := by sorry

alias «GroundTheory».«Heights₂».«Heights».«PeriodGramPosDef».«hermPair_symm» := P2M_GroundTheory_Heights__Heights_PeriodGramPosDef_hermPair_symm_5f1a589f163b
