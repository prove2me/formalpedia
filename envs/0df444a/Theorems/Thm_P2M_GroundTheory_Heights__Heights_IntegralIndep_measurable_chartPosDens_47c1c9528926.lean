-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_IntegralIndep_measurable_chartPosDens_47c1c9528926
-- name    : P2M_GroundTheory_Heights__Heights_IntegralIndep_measurable_chartPosDens_47c1c9528926
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-24T00:47:39.425192+00:00
-- url     : https://prove2.me/theorems/66968e81-79d4-4819-8ea7-1220ce28b666
-- title:
--   P2 M Ground Theory Heights  Heights Integral Indep measurable chart Pos Dens 47c1c9528926: P2 M Ground Theory Heights  Heights Integral Indep measurable chart Pos Dens 47c1c9528926
-- statement:
--   The P2 M Ground Theory Heights  Heights Integral Indep measurable chart Pos Dens 47c1c9528926 construction uses the P2 M Ground Theory Heights  Heights Integral Indep measurable chart Pos Dens 47c1c9528926 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ComplexAnalyticSets/PIntegralIndependent.lean#L37-L41
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ComplexAnalyticSets/PIntegralIndependent.lean#L37-L41

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

theorem P2M_GroundTheory_Heights__Heights_IntegralIndep_measurable_chartPosDens_47c1c9528926 {J : Ideal (MvPolynomial (Fin n) ℂ)} {A : Matrix (Fin d) (Fin n) ℂ}
    (hA : IsFiniteProjection J A) {f : (Fin n → ℂ) → ℝ} (hf : Measurable f)
    (φ : Fin d → (Fin n → ℂ) → ℝ) : Measurable (chartPosDens J A f φ) := by sorry

alias «GroundTheory».«Heights₂».«Heights».«IntegralIndep».«measurable_chartPosDens» := P2M_GroundTheory_Heights__Heights_IntegralIndep_measurable_chartPosDens_47c1c9528926
