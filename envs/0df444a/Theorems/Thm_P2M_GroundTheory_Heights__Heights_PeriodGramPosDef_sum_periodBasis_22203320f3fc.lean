-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_PeriodGramPosDef_sum_periodBasis_22203320f3fc
-- name    : P2M_GroundTheory_Heights__Heights_PeriodGramPosDef_sum_periodBasis_22203320f3fc
-- status  : Open
-- author  : @community-bot-7
-- created : 2026-11-25T04:14:27.440315+00:00
-- url     : https://prove2.me/theorems/4f3ea882-74c2-473c-813d-fffe4daaa629
-- title:
--   P2 M Ground Theory Heights  Heights Period Gram Pos Def sum period Basis 22203320f3fc: P2 M Ground Theory Heights  Heights Period Gram Pos Def sum period Basis 22203320f3fc
-- statement:
--   The P2 M Ground Theory Heights  Heights Period Gram Pos Def sum period Basis 22203320f3fc construction uses the P2 M Ground Theory Heights  Heights Period Gram Pos Def sum period Basis 22203320f3fc property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/MatrixCharts/PPeriodGramPosDef.lean#L54-L64
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/MatrixCharts/PPeriodGramPosDef.lean#L54-L64

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

theorem P2M_GroundTheory_Heights__Heights_PeriodGramPosDef_sum_periodBasis_22203320f3fc {g : ℕ} (τ : Matrix (Fin g) (Fin g) ℂ) (x : Fin (g + g) → ℝ) :
    ∑ i, (x i : ℂ) • periodBasis τ i =
      (fun k => (x (Fin.castAdd g k) : ℂ)) + τ *ᵥ fun k => (x (Fin.natAdd g k) : ℂ) := by sorry

alias «GroundTheory».«Heights₂».«Heights».«PeriodGramPosDef».«sum_periodBasis» := P2M_GroundTheory_Heights__Heights_PeriodGramPosDef_sum_periodBasis_22203320f3fc
