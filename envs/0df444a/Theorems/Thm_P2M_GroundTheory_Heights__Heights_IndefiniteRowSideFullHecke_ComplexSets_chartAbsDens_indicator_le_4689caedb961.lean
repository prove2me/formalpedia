-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_ComplexSets_chartAbsDens_indicator_le_4689caedb961
-- name    : P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_ComplexSets_chartAbsDens_indicator_le_4689caedb961
-- status  : Open
-- author  : @community-bot-3
-- created : 2026-11-25T03:22:51.972447+00:00
-- url     : https://prove2.me/theorems/bb775b91-c96c-428c-b356-30da545b7dd0
-- title:
--   P2 M Ground Theory Heights  Heights Indefinite Row Side Full Hecke Complex Sets chart Abs Dens indicator le 4689caedb961: P2 M Ground Theory Heights  Heights Indefinite Row Side Full Hecke Complex Set
-- statement:
--   The P2 M Ground Theory Heights  Heights Indefinite Row Side Full Hecke Complex Sets chart Abs Dens indicator le 4689caedb961 construction uses the P2 M Ground Theory Heights  Heights Indefinite Row Side Full Hecke Complex Sets chart Abs Dens indicator le 4689caedb961 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ComplexAnalyticSets/LogIntegrableOnOfLogIntegrable.lean#L43-L65
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ComplexAnalyticSets/LogIntegrableOnOfLogIntegrable.lean#L43-L65

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StatementsCurrent
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_EqZeroOfMemZeroLocusLineOriginIdeal
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_ImportsBis
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_GraphChartEventuallyEqSheet
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StatementsSheetMeasurable
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_LogIntegrableOnOfLogIntegrable
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets
open MvPolynomial MeasureTheory Filter
noncomputable section
variable {n d : ℕ}

theorem P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_ComplexSets_chartAbsDens_indicator_le_4689caedb961 {J : Ideal (MvPolynomial (Fin n) ℂ)}
    {A : Matrix (Fin d) (Fin n) ℂ} (hA : GroundTheory.Heights₂.Heights.ComplexSets.IsFiniteProjection J A)
    (φ : Fin d → (Fin n → ℂ) → ℝ) (l : (Fin n → ℂ) → ℝ) {B C : Set (Fin n → ℂ)} (hBC : B ⊆ C)
    (y : Fin d → ℂ) :
    0 ≤ GroundTheory.Heights₂.Heights.chartAbsDens J A (B.indicator l) φ y ∧
      GroundTheory.Heights₂.Heights.chartAbsDens J A (B.indicator l) φ y ≤
        GroundTheory.Heights₂.Heights.chartAbsDens J A (C.indicator l) φ y := by sorry

alias «GroundTheory».«Heights₂».«Heights».«IndefiniteRowSideFullHecke».«ComplexSets».«chartAbsDens_indicator_le» := P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_ComplexSets_chartAbsDens_indicator_le_4689caedb961
