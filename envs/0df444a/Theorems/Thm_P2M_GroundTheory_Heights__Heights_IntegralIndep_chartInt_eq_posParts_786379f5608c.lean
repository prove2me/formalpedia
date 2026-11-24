-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_IntegralIndep_chartInt_eq_posParts_786379f5608c
-- name    : P2M_GroundTheory_Heights__Heights_IntegralIndep_chartInt_eq_posParts_786379f5608c
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-24T01:11:07.107193+00:00
-- url     : https://prove2.me/theorems/67077516-7209-4e51-af0d-cfd994a8360b
-- title:
--   P2 M Ground Theory Heights  Heights Integral Indep chart Int eq pos Parts 786379f5608c: P2 M Ground Theory Heights  Heights Integral Indep chart Int eq pos Parts 786379f5608c
-- statement:
--   The P2 M Ground Theory Heights  Heights Integral Indep chart Int eq pos Parts 786379f5608c construction uses the P2 M Ground Theory Heights  Heights Integral Indep chart Int eq pos Parts 786379f5608c property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ComplexAnalyticSets/PIntegralIndependent.lean#L43-L79
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ComplexAnalyticSets/PIntegralIndependent.lean#L43-L79

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

theorem P2M_GroundTheory_Heights__Heights_IntegralIndep_chartInt_eq_posParts_786379f5608c {J : Ideal (MvPolynomial (Fin n) ℂ)} {A : Matrix (Fin d) (Fin n) ℂ}
    (hA : IsFiniteProjection J A) {f : (Fin n → ℂ) → ℝ} (hf : Measurable f)
    (φ : Fin d → (Fin n → ℂ) → ℝ) :
    (Integrable (chartAbsDens J A f φ) ↔
      (∫⁻ y, ENNReal.ofReal (chartPosDens J A f φ y)) +
        ∫⁻ y, ENNReal.ofReal (chartPosDens J A (-f) φ y) < ⊤) ∧
    (Integrable (chartAbsDens J A f φ) → chartInt J A f φ =
      (∫⁻ y, ENNReal.ofReal (chartPosDens J A f φ y)).toReal -
        (∫⁻ y, ENNReal.ofReal (chartPosDens J A (-f) φ y)).toReal) := by sorry

alias «GroundTheory».«Heights₂».«Heights».«IntegralIndep».«chartInt_eq_posParts» := P2M_GroundTheory_Heights__Heights_IntegralIndep_chartInt_eq_posParts_786379f5608c
