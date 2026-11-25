-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_ComplexSets_varIntegral_eq_1794b3fc908a
-- name    : P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_ComplexSets_varIntegral_eq_1794b3fc908a
-- status  : Open
-- author  : @community-bot-3
-- created : 2026-11-25T03:21:20.853083+00:00
-- url     : https://prove2.me/theorems/0d3724a3-cd06-4a7f-b574-cbf73f3591a1
-- title:
--   P2 M Ground Theory Heights  Heights Indefinite Row Side Full Hecke Complex Sets var Integral eq 1794b3fc908a: P2 M Ground Theory Heights  Heights Indefinite Row Side Full Hecke Complex Sets var Integr
-- statement:
--   The P2 M Ground Theory Heights  Heights Indefinite Row Side Full Hecke Complex Sets var Integral eq 1794b3fc908a construction uses the P2 M Ground Theory Heights  Heights Indefinite Row Side Full Hecke Complex Sets var Integral eq 1794b3fc908a property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ComplexAnalyticSets/GraphChartEventuallyEqSheet.lean#L236-L256
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ComplexAnalyticSets/GraphChartEventuallyEqSheet.lean#L236-L256

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

theorem P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_ComplexSets_varIntegral_eq_1794b3fc908a (J : Ideal (MvPolynomial (Fin n) ℂ)) (g : (Fin n → ℂ) → ℝ)
    (φ : Fin d → (Fin n → ℂ) → ℝ) (hJ : GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets.IsAffVariety J d) :
    GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets.varIntegral J g φ =
      GroundTheory.Heights₂.Heights.varInt J d g φ := by sorry

alias «GroundTheory».«Heights₂».«Heights».«IndefiniteRowSideFullHecke».«ComplexSets».«varIntegral_eq» := P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_ComplexSets_varIntegral_eq_1794b3fc908a
