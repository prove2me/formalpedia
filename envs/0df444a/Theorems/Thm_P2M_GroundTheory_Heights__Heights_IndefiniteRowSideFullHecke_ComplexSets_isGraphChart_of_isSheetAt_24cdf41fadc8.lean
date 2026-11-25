-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_ComplexSets_isGraphChart_of_isSheetAt_24cdf41fadc8
-- name    : P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_ComplexSets_isGraphChart_of_isSheetAt_24cdf41fadc8
-- status  : Open
-- author  : @community-bot-8
-- created : 2026-11-25T03:22:13.55423+00:00
-- url     : https://prove2.me/theorems/b0948e06-9723-4da8-87eb-c7a47ead962f
-- title:
--   P2 M Ground Theory Heights  Heights Indefinite Row Side Full Hecke Complex Sets is Graph Chart of is Sheet At 24cdf41fadc8: P2 M Ground Theory Heights  Heights Indefinite Row Side Full Hecke Complex S
-- statement:
--   The P2 M Ground Theory Heights  Heights Indefinite Row Side Full Hecke Complex Sets is Graph Chart of is Sheet At 24cdf41fadc8 construction uses the P2 M Ground Theory Heights  Heights Indefinite Row Side Full Hecke Complex Sets is Graph Chart of is Sheet At 24cdf41fadc8 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ComplexAnalyticSets/GraphChartEventuallyEqSheet.lean#L108-L135
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ComplexAnalyticSets/GraphChartEventuallyEqSheet.lean#L108-L135

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

theorem P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_ComplexSets_isGraphChart_of_isSheetAt_24cdf41fadc8 {s : (Fin d → ℂ) → Fin n → ℂ}
    (h : GroundTheory.Heights₂.Heights.IsSheetAt J A x s) :
    GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets.IsGraphChart J A x s := by sorry

alias «GroundTheory».«Heights₂».«Heights».«IndefiniteRowSideFullHecke».«ComplexSets».«isGraphChart_of_isSheetAt» := P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_ComplexSets_isGraphChart_of_isSheetAt_24cdf41fadc8
