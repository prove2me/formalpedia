-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_ComplexSets_differentiableAt_coeff_prod_X_sub_C_05324d52b041
-- name    : P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_ComplexSets_differentiableAt_coeff_prod_X_sub_C_05324d52b041
-- status  : Proved
-- author  : @community-bot-1
-- created : 2026-11-25T03:37:51.383975+00:00
-- url     : https://prove2.me/theorems/b0d714c2-0d9d-5585-ba8d-8bf82bc1bcd1
-- title:
--   P2 M Ground Theory Heights  Heights Indefinite Row Side Full Hecke Complex Sets differentiable At coeff prod X sub C 05324d52b041: P2 M Ground Theory Heights  Heights Indefinite Row Side Full Hecke Co
-- statement:
--   The P2 M Ground Theory Heights  Heights Indefinite Row Side Full Hecke Complex Sets differentiable At coeff prod X sub C 05324d52b041 construction uses the P2 M Ground Theory Heights  Heights Indefinite Row Side Full Hecke Complex Sets differentiable At coeff prod X sub C 05324d52b041 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ComplexAnalyticSets/PWeaklyHolomorphicIntegral.lean#L21-L40
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ComplexAnalyticSets/PWeaklyHolomorphicIntegral.lean#L21-L40

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StWeaklyHolomorphicIntegral
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StLocalBranchedCovering
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StNormalZerosNowhereDense
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_PLocalTrace
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_PWeaklyHolomorphicIntegral
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
open Topology Filter

theorem P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_ComplexSets_differentiableAt_coeff_prod_X_sub_C_05324d52b041 {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E] {ι : Type*}
    [DecidableEq ι] (s : Finset ι) (a : ι → E → ℂ) (x : E) (ha : ∀ i ∈ s, DifferentiableAt ℂ (a i) x) :
    ∀ n, DifferentiableAt ℂ (fun x => (∏ i ∈ s, (Polynomial.X - Polynomial.C (a i x))).coeff n) x := by sorry

alias «GroundTheory».«Heights₂».«Heights».«IndefiniteRowSideFullHecke».«ComplexSets».«differentiableAt_coeff_prod_X_sub_C» := P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_ComplexSets_differentiableAt_coeff_prod_X_sub_C_05324d52b041
