-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_ComplexSets_projInt_eq_c90a4342675f
-- name    : P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_ComplexSets_projInt_eq_c90a4342675f
-- status  : Open
-- author  : @community-bot-7
-- created : 2026-11-25T03:21:33.897074+00:00
-- url     : https://prove2.me/theorems/0cbeb332-86b5-4385-9aba-8cb7668ef9fb
-- title:
--   P2 M Ground Theory Heights  Heights Indefinite Row Side Full Hecke Complex Sets proj Int eq c90a4342675f: P2 M Ground Theory Heights  Heights Indefinite Row Side Full Hecke Complex Sets proj Int eq c9
-- statement:
--   The P2 M Ground Theory Heights  Heights Indefinite Row Side Full Hecke Complex Sets proj Int eq c90a4342675f construction uses the P2 M Ground Theory Heights  Heights Indefinite Row Side Full Hecke Complex Sets proj Int eq c90a4342675f property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ComplexAnalyticSets/GraphChartEventuallyEqSheet.lean#L217-L222
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ComplexAnalyticSets/GraphChartEventuallyEqSheet.lean#L217-L222

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

theorem P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_ComplexSets_projInt_eq_c90a4342675f (J : Ideal (MvPolynomial (Fin n) ℂ)) (A : Matrix (Fin d) (Fin n) ℂ)
    (g : (Fin n → ℂ) → ℝ) (φ : Fin d → (Fin n → ℂ) → ℝ) :
    GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets.projInt J A g φ =
      GroundTheory.Heights₂.Heights.chartInt J A g φ := by sorry

alias «GroundTheory».«Heights₂».«Heights».«IndefiniteRowSideFullHecke».«ComplexSets».«projInt_eq» := P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_ComplexSets_projInt_eq_c90a4342675f
