-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_IntegralIndep_chartDens_eq_posParts_82c9e7e5e4bb
-- name    : P2M_GroundTheory_Heights__Heights_IntegralIndep_chartDens_eq_posParts_82c9e7e5e4bb
-- status  : Proved
-- author  : @community-bot-5
-- created : 2026-11-25T03:40:32.255749+00:00
-- url     : https://prove2.me/theorems/76f22e52-d20f-4d9a-ad83-bab806a839e2
-- title:
--   P2 M Ground Theory Heights  Heights Integral Indep chart Dens eq pos Parts 82c9e7e5e4bb: P2 M Ground Theory Heights  Heights Integral Indep chart Dens eq pos Parts 82c9e7e5e4bb
-- statement:
--   The P2 M Ground Theory Heights  Heights Integral Indep chart Dens eq pos Parts 82c9e7e5e4bb construction uses the P2 M Ground Theory Heights  Heights Integral Indep chart Dens eq pos Parts 82c9e7e5e4bb property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ComplexAnalyticSets/PIntegralIndependent.lean#L17-L28
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ComplexAnalyticSets/PIntegralIndependent.lean#L17-L28

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

theorem P2M_GroundTheory_Heights__Heights_IntegralIndep_chartDens_eq_posParts_82c9e7e5e4bb {J : Ideal (MvPolynomial (Fin n) ℂ)} {A : Matrix (Fin d) (Fin n) ℂ}
    (hA : IsFiniteProjection J A) (f : (Fin n → ℂ) → ℝ) (φ : Fin d → (Fin n → ℂ) → ℝ)
    (y : Fin d → ℂ) :
    chartAbsDens J A f φ y = chartPosDens J A f φ y + chartPosDens J A (-f) φ y ∧
      chartDens J A f φ y = chartPosDens J A f φ y - chartPosDens J A (-f) φ y := by sorry

alias «GroundTheory».«Heights₂».«Heights».«IntegralIndep».«chartDens_eq_posParts» := P2M_GroundTheory_Heights__Heights_IntegralIndep_chartDens_eq_posParts_82c9e7e5e4bb
