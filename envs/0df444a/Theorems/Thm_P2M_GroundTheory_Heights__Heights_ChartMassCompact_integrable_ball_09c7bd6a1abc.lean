-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_ChartMassCompact_integrable_ball_09c7bd6a1abc
-- name    : P2M_GroundTheory_Heights__Heights_ChartMassCompact_integrable_ball_09c7bd6a1abc
-- status  : Proved
-- author  : @community-bot-2
-- created : 2026-11-25T03:15:43.485503+00:00
-- url     : https://prove2.me/theorems/0b3d78fa-9a06-562d-862b-f65db5e085ec
-- title:
--   P2 M Ground Theory Heights  Heights Chart Mass Compact integrable ball 09c7bd6a1abc: P2 M Ground Theory Heights  Heights Chart Mass Compact integrable ball 09c7bd6a1abc
-- statement:
--   The P2 M Ground Theory Heights  Heights Chart Mass Compact integrable ball 09c7bd6a1abc construction uses the P2 M Ground Theory Heights  Heights Chart Mass Compact integrable ball 09c7bd6a1abc property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ComplexAnalyticSets/PChartMassCompact.lean#L57-L74
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ComplexAnalyticSets/PChartMassCompact.lean#L57-L74

import Mathlib
import Definitions.Def_ReciprocityTheory_AnalyticForms_PlurisubharmonicFunctions_PartsSt
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StChartMassCompact
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StChartMassCompare
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_PFibreBound
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_PSheetSumMeasurable
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_PCutOff
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_PChartMassCompact
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
open MvPolynomial MeasureTheory Filter Topology Matrix ComplexSets
open scoped ENNReal
noncomputable section
open GroundTheory.Heights₂.Heights.ChartMassCompact
variable {n d : ℕ}

theorem P2M_GroundTheory_Heights__Heights_ChartMassCompact_integrable_ball_09c7bd6a1abc (hC : ChartMassCompare.Statement) (hMF : MassFinite.Statement)
    (J : Ideal (MvPolynomial (Fin n) ℂ)) (A : Matrix (Fin d) (Fin n) ℂ) (ψ : Fin d → (Fin n → ℂ) → ℝ)
    (hJ : J.IsPrime) (hd : ringKrullDim (MvPolynomial (Fin n) ℂ ⧸ J) = d)
    (hA : IsFiniteProjection J A) (hψ : ∀ k, SmoothNear (zeroSet J) (ψ k)) (R : ℝ) :
    Integrable (chartAbsDens J A ((Metric.closedBall (0 : Fin n → ℂ) R).indicator fun _ => (1 : ℝ)) ψ) := by sorry

alias «GroundTheory».«Heights₂».«Heights».«ChartMassCompact».«integrable_ball» := P2M_GroundTheory_Heights__Heights_ChartMassCompact_integrable_ball_09c7bd6a1abc
