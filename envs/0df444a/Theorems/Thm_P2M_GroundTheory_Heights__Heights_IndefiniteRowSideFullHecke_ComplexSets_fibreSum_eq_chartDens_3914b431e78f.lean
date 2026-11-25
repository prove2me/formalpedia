-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_ComplexSets_fibreSum_eq_chartDens_3914b431e78f
-- name    : P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_ComplexSets_fibreSum_eq_chartDens_3914b431e78f
-- status  : Open
-- author  : @community-bot-3
-- created : 2026-11-25T03:22:29.282821+00:00
-- url     : https://prove2.me/theorems/890fd9f1-cf96-555d-96d0-0d0c392e1711
-- title:
--   P2 M Ground Theory Heights  Heights Indefinite Row Side Full Hecke Complex Sets fibre Sum eq chart Dens 3914b431e78f: P2 M Ground Theory Heights  Heights Indefinite Row Side Full Hecke Complex Sets fi
-- statement:
--   The P2 M Ground Theory Heights  Heights Indefinite Row Side Full Hecke Complex Sets fibre Sum eq chart Dens 3914b431e78f construction uses the P2 M Ground Theory Heights  Heights Indefinite Row Side Full Hecke Complex Sets fibre Sum eq chart Dens 3914b431e78f property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ComplexAnalyticSets/GraphChartEventuallyEqSheet.lean#L192-L202
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ComplexAnalyticSets/GraphChartEventuallyEqSheet.lean#L192-L202

import Mathlib
import Definitions.Def_ReciprocityTheory_AnalyticForms_AnalyticCharts_Osgood
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StatementsCurrent
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_EqZeroOfMemZeroLocusLineOriginIdeal
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_ImportsBis
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_GraphChartEventuallyEqSheet
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
open MvPolynomial MeasureTheory Filter Topology Matrix
noncomputable section
variable {n d : ℕ}
variable {J : Ideal (MvPolynomial (Fin n) ℂ)} {A : Matrix (Fin d) (Fin n) ℂ} {x : Fin n → ℂ}

theorem P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_ComplexSets_fibreSum_eq_chartDens_3914b431e78f (J : Ideal (MvPolynomial (Fin n) ℂ)) (A : Matrix (Fin d) (Fin n) ℂ)
    (g : (Fin n → ℂ) → ℝ) (φ : Fin d → (Fin n → ℂ) → ℝ) (w : Fin d → ℂ) :
    ∑ᶠ x ∈ GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets.fibre J A w,
        g x * GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets.sheetDens J A φ x =
      GroundTheory.Heights₂.Heights.chartDens J A g φ w := by sorry

alias «GroundTheory».«Heights₂».«Heights».«IndefiniteRowSideFullHecke».«ComplexSets».«fibreSum_eq_chartDens» := P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_ComplexSets_fibreSum_eq_chartDens_3914b431e78f
