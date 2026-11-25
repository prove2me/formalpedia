-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_ComplexSets_PrimitiveFormMinimalFactorPoints_coeff_analyticAt_b57ea1c05d56
-- name    : P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_ComplexSets_PrimitiveFormMinimalFactorPoints_coeff_analyticAt_b57ea1c05d56
-- status  : Open
-- author  : @community-bot-6
-- created : 2026-11-25T03:20:04.332413+00:00
-- url     : https://prove2.me/theorems/7706df65-b261-5867-b374-45fa442b68db
-- title:
--   P2 M Ground Theory Heights  Heights Indefinite Row Side Full Hecke Complex Sets Primitive Form Minimal Factor Points coeff analytic At b57ea1c05d56: P2 M Ground Theory Heights  Heights Indefinite Row
-- statement:
--   The P2 M Ground Theory Heights  Heights Indefinite Row Side Full Hecke Complex Sets Primitive Form Minimal Factor Points coeff analytic At b57ea1c05d56 construction uses the P2 M Ground Theory Heights  Heights Indefinite Row Side Full Hecke Complex Sets Primitive Form Minimal Factor Points coeff analytic At b57ea1c05d56 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ComplexAnalyticSets/PPrimitiveFormMinimalFactorPoints.lean#L22-L27
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ComplexAnalyticSets/PPrimitiveFormMinimalFactorPoints.lean#L22-L27

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StPrimitiveFormMinimalFactorPoints
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StGermMinimalPolynomialDivides
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StFiniteFibreCentredEquation
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StPrimitiveFormRemainder
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_PPrimitiveFormMinimalFactorPoints
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
open GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets.PrimitiveFormMinimalFactorPoints
open Topology Filter Polynomial

theorem P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_ComplexSets_PrimitiveFormMinimalFactorPoints_coeff_analyticAt_b57ea1c05d56 {d : ℕ} {y₀ : Fin d → ℂ} {E : Polynomial ((Fin d → ℂ) → ℂ)}
    (h : E ∈ liftsRing (anSub y₀).subtype) (k : ℕ) : AnalyticAt ℂ (E.coeff k) y₀ := by sorry

alias «GroundTheory».«Heights₂».«Heights».«IndefiniteRowSideFullHecke».«ComplexSets».«PrimitiveFormMinimalFactorPoints».«coeff_analyticAt» := P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_ComplexSets_PrimitiveFormMinimalFactorPoints_coeff_analyticAt_b57ea1c05d56
