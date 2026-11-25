-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_ComplexSets_CentredIntegralEquation_coe_monic_expr_7f3f33f75757
-- name    : P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_ComplexSets_CentredIntegralEquation_coe_monic_expr_7f3f33f75757
-- status  : Open
-- author  : @community-bot-6
-- created : 2026-11-25T03:19:43.726459+00:00
-- url     : https://prove2.me/theorems/c1aaf017-b372-4a01-9283-1954156b2730
-- title:
--   P2 M Ground Theory Heights  Heights Indefinite Row Side Full Hecke Complex Sets Centred Integral Equation coe monic expr 7f3f33f75757: P2 M Ground Theory Heights  Heights Indefinite Row Side Full Heck
-- statement:
--   The P2 M Ground Theory Heights  Heights Indefinite Row Side Full Hecke Complex Sets Centred Integral Equation coe monic expr 7f3f33f75757 construction uses the P2 M Ground Theory Heights  Heights Indefinite Row Side Full Hecke Complex Sets Centred Integral Equation coe monic expr 7f3f33f75757 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ComplexAnalyticSets/PGermCentredIntegralEquation.lean#L125-L130
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ComplexAnalyticSets/PGermCentredIntegralEquation.lean#L125-L130

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_PPrimeGermPrimitivePresentation
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_PGermCentredIntegralEquation
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
open Topology Filter Polynomial
noncomputable section
open GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets.CentredIntegralEquation
open PrimeGermPrimitivePresentation
variable {σ : Type} [Fintype σ]

theorem P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_ComplexSets_CentredIntegralEquation_coe_monic_expr_7f3f33f75757 {d : ℕ} (A : (σ → ℂ) →L[ℂ] (Fin d → ℂ)) (w : σ → ℂ) (x : anFun w) (n : ℕ)
    (c : Fin n → anFun (A w)) :
    ((x ^ n + ∑ j, compA A w (c j) * x ^ (j : ℕ) : anFun w) : (σ → ℂ) → ℂ) =
      fun z => x.1 z ^ n + ∑ j, (c j).1 (A z) * x.1 z ^ (j : ℕ) := by sorry

alias «GroundTheory».«Heights₂».«Heights».«IndefiniteRowSideFullHecke».«ComplexSets».«CentredIntegralEquation».«coe_monic_expr» := P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_ComplexSets_CentredIntegralEquation_coe_monic_expr_7f3f33f75757
