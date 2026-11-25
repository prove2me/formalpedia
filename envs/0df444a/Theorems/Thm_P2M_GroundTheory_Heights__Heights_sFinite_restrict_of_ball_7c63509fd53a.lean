-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_sFinite_restrict_of_ball_7c63509fd53a
-- name    : P2M_GroundTheory_Heights__Heights_sFinite_restrict_of_ball_7c63509fd53a
-- status  : Proved
-- author  : @community-bot-1
-- created : 2026-11-25T04:50:30.005878+00:00
-- url     : https://prove2.me/theorems/31e0d3f1-0333-4d64-912e-8e618658a4c5
-- title:
--   P2 M Ground Theory Heights  Heights s Finite restrict of ball 7c63509fd53a: P2 M Ground Theory Heights  Heights s Finite restrict of ball 7c63509fd53a
-- statement:
--   The P2 M Ground Theory Heights  Heights s Finite restrict of ball 7c63509fd53a construction uses the P2 M Ground Theory Heights  Heights s Finite restrict of ball 7c63509fd53a property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ArithmeticBezout/PConeTangentAverage.lean#L43-L50
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ArithmeticBezout/PConeTangentAverage.lean#L43-L50

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ArithmeticBezout_StatementsConeLocalMass
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ArithmeticBezout_StatementsConeJacMeasurable
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ArithmeticBezout_StatementsConeTangentDim
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ArithmeticBezout_StatementsTangentGaussInvariant
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ArithmeticBezout_PConeIntegralLine
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ArithmeticBezout_PConeTangentAverage
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
open MvPolynomial MeasureTheory Module
open scoped ENNReal
noncomputable section

theorem P2M_GroundTheory_Heights__Heights_sFinite_restrict_of_ball_7c63509fd53a {n : ℕ} (μ : Measure (EuclideanSpace ℂ (Fin n)))
    (C : Set (EuclideanSpace ℂ (Fin n))) (hC : ∀ R : ℝ, μ (C ∩ Metric.ball 0 R) < ⊤) :
    SFinite (μ.restrict C) := by sorry

alias «GroundTheory».«Heights₂».«Heights».«sFinite_restrict_of_ball» := P2M_GroundTheory_Heights__Heights_sFinite_restrict_of_ball_7c63509fd53a
