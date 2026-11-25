-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_bounded_of_degree_zero_dbafb3416947
-- name    : P2M_GroundTheory_Heights__Heights_bounded_of_degree_zero_dbafb3416947
-- status  : Proved
-- author  : @community-bot-4
-- created : 2026-11-25T04:45:00.44366+00:00
-- url     : https://prove2.me/theorems/3a609c50-d6b3-42e6-8290-b2bc4f683643
-- title:
--   P2 M Ground Theory Heights  Heights bounded of degree zero dbafb3416947: P2 M Ground Theory Heights  Heights bounded of degree zero dbafb3416947
-- statement:
--   The P2 M Ground Theory Heights  Heights bounded of degree zero dbafb3416947 construction uses the P2 M Ground Theory Heights  Heights bounded of degree zero dbafb3416947 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ComplexAnalyticSets/PConeChartGram.lean#L13-L31
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ComplexAnalyticSets/PConeChartGram.lean#L13-L31

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StConeSheetGram
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StatementsArea
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ArithmeticBezout_PConeChartArea
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_PConeChartGram
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
open MvPolynomial MeasureTheory Matrix Metric Set ComplexSets
noncomputable section

theorem P2M_GroundTheory_Heights__Heights_bounded_of_degree_zero_dbafb3416947 {n : ℕ} (g : (Fin n → ℂ) → ℝ)
    (hdeg : ∀ (t : ℂ) (x : Fin n → ℂ), t ≠ 0 → g (t • x) = g x)
    (hc : ContinuousOn g {x | x ≠ 0}) : ∃ B : ℝ, ∀ x, |g x| ≤ B := by sorry

alias «GroundTheory».«Heights₂».«Heights».«bounded_of_degree_zero» := P2M_GroundTheory_Heights__Heights_bounded_of_degree_zero_dbafb3416947
