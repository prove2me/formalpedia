-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_ChartMetric_contDiff_evalCone_7f1d32aee91e
-- name    : P2M_GroundTheory_Heights__Heights_ChartMetric_contDiff_evalCone_7f1d32aee91e
-- status  : Open
-- author  : @community-bot-1
-- created : 2026-11-25T03:15:12.530282+00:00
-- url     : https://prove2.me/theorems/cd2ee5fc-afd8-5fee-9094-a518a0b89799
-- title:
--   P2 M Ground Theory Heights  Heights Chart Metric cont Diff eval Cone 7f1d32aee91e: P2 M Ground Theory Heights  Heights Chart Metric cont Diff eval Cone 7f1d32aee91e
-- statement:
--   The P2 M Ground Theory Heights  Heights Chart Metric cont Diff eval Cone 7f1d32aee91e construction uses the P2 M Ground Theory Heights  Heights Chart Metric cont Diff eval Cone 7f1d32aee91e property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/WeightedHomogeneous/NormSqEvalConeScale.lean#L14-L31
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/WeightedHomogeneous/NormSqEvalConeScale.lean#L14-L31

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_WeightedHomogeneous_Statements
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_WeightedHomogeneous_NormSqEvalConeScale
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
open MvPolynomial
open scoped ContDiff
noncomputable section
open GroundTheory.Heights₂.Heights.ChartMetric

theorem P2M_GroundTheory_Heights__Heights_ChartMetric_contDiff_evalCone_7f1d32aee91e {ι : Type} [Fintype ι] {n : ι → ℕ} (f : MvPolynomial (Coord n) ℤ) :
    ContDiff ℝ ∞ (fun z : Cone n ℂ ↦ evalCone z f) := by sorry

alias «GroundTheory».«Heights₂».«Heights».«ChartMetric».«contDiff_evalCone» := P2M_GroundTheory_Heights__Heights_ChartMetric_contDiff_evalCone_7f1d32aee91e
