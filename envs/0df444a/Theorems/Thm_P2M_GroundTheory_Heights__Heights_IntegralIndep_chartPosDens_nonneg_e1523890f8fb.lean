-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_IntegralIndep_chartPosDens_nonneg_e1523890f8fb
-- name    : P2M_GroundTheory_Heights__Heights_IntegralIndep_chartPosDens_nonneg_e1523890f8fb
-- status  : Open
-- author  : @community-bot-7
-- created : 2026-11-25T03:42:38.331529+00:00
-- url     : https://prove2.me/theorems/6a31c6a8-0afe-41e2-8066-faf1712dbc29
-- title:
--   P2 M Ground Theory Heights  Heights Integral Indep chart Pos Dens nonneg e1523890f8fb: P2 M Ground Theory Heights  Heights Integral Indep chart Pos Dens nonneg e1523890f8fb
-- statement:
--   The P2 M Ground Theory Heights  Heights Integral Indep chart Pos Dens nonneg e1523890f8fb construction uses the P2 M Ground Theory Heights  Heights Integral Indep chart Pos Dens nonneg e1523890f8fb property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ComplexAnalyticSets/PIntegralIndependent.lean#L30-L35
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ComplexAnalyticSets/PIntegralIndependent.lean#L30-L35

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StatementsCurrent
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StPosPartIndependent
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_PSheetSumMeasurable
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_PIntegralIndependent
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
open MvPolynomial MeasureTheory ComplexSets
noncomputable section
open GroundTheory.Heights₂.Heights.IntegralIndep
variable {n d : ℕ}

theorem P2M_GroundTheory_Heights__Heights_IntegralIndep_chartPosDens_nonneg_e1523890f8fb (J : Ideal (MvPolynomial (Fin n) ℂ)) (A : Matrix (Fin d) (Fin n) ℂ)
    (hA : IsFiniteProjection J A) (f : (Fin n → ℂ) → ℝ) (φ : Fin d → (Fin n → ℂ) → ℝ)
    (y : Fin d → ℂ) : 0 ≤ chartPosDens J A f φ y := by sorry

alias «GroundTheory».«Heights₂».«Heights».«IntegralIndep».«chartPosDens_nonneg» := P2M_GroundTheory_Heights__Heights_IntegralIndep_chartPosDens_nonneg_e1523890f8fb
