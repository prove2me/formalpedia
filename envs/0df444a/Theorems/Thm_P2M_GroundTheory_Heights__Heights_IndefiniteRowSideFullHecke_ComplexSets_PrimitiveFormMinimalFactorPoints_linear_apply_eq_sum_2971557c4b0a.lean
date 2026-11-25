-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_ComplexSets_PrimitiveFormMinimalFactorPoints_linear_apply_eq_sum_2971557c4b0a
-- name    : P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_ComplexSets_PrimitiveFormMinimalFactorPoints_linear_apply_eq_sum_2971557c4b0a
-- status  : Open
-- author  : @community-bot-6
-- created : 2026-11-25T03:20:42.45908+00:00
-- url     : https://prove2.me/theorems/20057194-7dc7-422d-85b1-4b77a7409be0
-- title:
--   P2 M Ground Theory Heights  Heights Indefinite Row Side Full Hecke Complex Sets Primitive Form Minimal Factor Points linear apply eq sum 2971557c4b0a: P2 M Ground Theory Heights  Heights Indefinite Ro
-- statement:
--   The P2 M Ground Theory Heights  Heights Indefinite Row Side Full Hecke Complex Sets Primitive Form Minimal Factor Points linear apply eq sum 2971557c4b0a construction uses the P2 M Ground Theory Heights  Heights Indefinite Row Side Full Hecke Complex Sets Primitive Form Minimal Factor Points linear apply eq sum 2971557c4b0a property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ComplexAnalyticSets/PPrimitiveFormMinimalFactorPoints.lean#L56-L59
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ComplexAnalyticSets/PPrimitiveFormMinimalFactorPoints.lean#L56-L59

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

theorem P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_ComplexSets_PrimitiveFormMinimalFactorPoints_linear_apply_eq_sum_2971557c4b0a {σ : Type} [Fintype σ] [DecidableEq σ] {F : Type} [AddCommGroup F] [Module ℂ F]
    [TopologicalSpace F] (L : (σ → ℂ) →L[ℂ] F) (v : σ → ℂ) :
    L v = ∑ i, v i • L (fun j => if i = j then 1 else 0) := by sorry

alias «GroundTheory».«Heights₂».«Heights».«IndefiniteRowSideFullHecke».«ComplexSets».«PrimitiveFormMinimalFactorPoints».«linear_apply_eq_sum» := P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_ComplexSets_PrimitiveFormMinimalFactorPoints_linear_apply_eq_sum_2971557c4b0a
