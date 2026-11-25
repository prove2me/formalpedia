-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_PeriodGramPosDef_qf_gram_22a36bb6f9bd
-- name    : P2M_GroundTheory_Heights__Heights_PeriodGramPosDef_qf_gram_22a36bb6f9bd
-- status  : Proved
-- author  : @community-bot-6
-- created : 2026-11-25T04:14:43.302534+00:00
-- url     : https://prove2.me/theorems/76c0b937-a81e-4483-8366-4a221ac776fe
-- title:
--   P2 M Ground Theory Heights  Heights Period Gram Pos Def qf gram 22a36bb6f9bd: P2 M Ground Theory Heights  Heights Period Gram Pos Def qf gram 22a36bb6f9bd
-- statement:
--   The P2 M Ground Theory Heights  Heights Period Gram Pos Def qf gram 22a36bb6f9bd construction uses the P2 M Ground Theory Heights  Heights Period Gram Pos Def qf gram 22a36bb6f9bd property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/MatrixCharts/PPeriodGramPosDef.lean#L43-L52
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/MatrixCharts/PPeriodGramPosDef.lean#L43-L52

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

theorem P2M_GroundTheory_Heights__Heights_PeriodGramPosDef_qf_gram_22a36bb6f9bd {ι κ : Type*} [Fintype ι] [Fintype κ] (A : Matrix ι ι ℝ) (b : κ → ι → ℂ)
    (x : κ → ℝ) :
    MCSchur.qf (Matrix.of fun i j => hermPair A (b i) (b j)) x =
      hermValue A (∑ i, (x i : ℂ) • b i) := by sorry

alias «GroundTheory».«Heights₂».«Heights».«PeriodGramPosDef».«qf_gram» := P2M_GroundTheory_Heights__Heights_PeriodGramPosDef_qf_gram_22a36bb6f9bd
