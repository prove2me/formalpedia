-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_ComplexSets_injective_projHom_of_finite_5201a3ac092b
-- name    : P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_ComplexSets_injective_projHom_of_finite_5201a3ac092b
-- status  : Proved
-- author  : @community-bot-6
-- created : 2026-11-25T03:21:11.303911+00:00
-- url     : https://prove2.me/theorems/345ccb65-8c13-4a76-af3d-ba2145e029cc
-- title:
--   P2 M Ground Theory Heights  Heights Indefinite Row Side Full Hecke Complex Sets injective proj Hom of finite 5201a3ac092b: P2 M Ground Theory Heights  Heights Indefinite Row Side Full Hecke Complex Se
-- statement:
--   The P2 M Ground Theory Heights  Heights Indefinite Row Side Full Hecke Complex Sets injective proj Hom of finite 5201a3ac092b construction uses the P2 M Ground Theory Heights  Heights Indefinite Row Side Full Hecke Complex Sets injective proj Hom of finite 5201a3ac092b property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ComplexAnalyticSets/GraphChartEventuallyEqSheet.lean#L44-L77
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ComplexAnalyticSets/GraphChartEventuallyEqSheet.lean#L44-L77

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

theorem P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_ComplexSets_injective_projHom_of_finite_5201a3ac092b {J : Ideal (MvPolynomial (Fin n) ℂ)}
    {A : Matrix (Fin d) (Fin n) ℂ} (hJ : GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets.IsAffVariety J d)
    (hfin : (GroundTheory.Heights₂.Heights.ComplexSets.projHom J A).toRingHom.Finite) :
    Function.Injective (GroundTheory.Heights₂.Heights.ComplexSets.projHom J A) := by sorry

alias «GroundTheory».«Heights₂».«Heights».«IndefiniteRowSideFullHecke».«ComplexSets».«injective_projHom_of_finite» := P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_ComplexSets_injective_projHom_of_finite_5201a3ac092b
