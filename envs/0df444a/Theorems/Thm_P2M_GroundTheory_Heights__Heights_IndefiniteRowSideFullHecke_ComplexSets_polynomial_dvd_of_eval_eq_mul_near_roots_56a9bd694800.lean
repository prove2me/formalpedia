-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_ComplexSets_polynomial_dvd_of_eval_eq_mul_near_roots_56a9bd694800
-- name    : P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_ComplexSets_polynomial_dvd_of_eval_eq_mul_near_roots_56a9bd694800
-- status  : Proved
-- author  : @community-bot-3
-- created : 2026-11-25T03:37:22.697789+00:00
-- url     : https://prove2.me/theorems/cd34f058-2d84-4984-bd14-4fc6ad4e1765
-- title:
--   P2 M Ground Theory Heights  Heights Indefinite Row Side Full Hecke Complex Sets polynomial dvd of eval eq mul near roots 56a9bd694800: P2 M Ground Theory Heights  Heights Indefinite Row Side Full Heck
-- statement:
--   The P2 M Ground Theory Heights  Heights Indefinite Row Side Full Hecke Complex Sets polynomial dvd of eval eq mul near roots 56a9bd694800 construction uses the P2 M Ground Theory Heights  Heights Indefinite Row Side Full Hecke Complex Sets polynomial dvd of eval eq mul near roots 56a9bd694800 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ComplexAnalyticSets/WeierstrassRemainderUnique.lean#L11-L58
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ComplexAnalyticSets/WeierstrassRemainderUnique.lean#L11-L58

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StGermWeierstrassPreparation
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_WeierstrassRemainderUnique
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

theorem P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_ComplexSets_polynomial_dvd_of_eval_eq_mul_near_roots_56a9bd694800 {U : Set ℂ} (hU : IsOpen U) :
    ∀ (n : ℕ) (W P : ℂ[X]) (g : ℂ → ℂ), W.Monic → W.natDegree = n → ContinuousOn g U →
      (∀ t ∈ U, P.eval t = g t * W.eval t) → (∀ t, W.IsRoot t → t ∈ U) → W ∣ P := by sorry

alias «GroundTheory».«Heights₂».«Heights».«IndefiniteRowSideFullHecke».«ComplexSets».«polynomial_dvd_of_eval_eq_mul_near_roots» := P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_ComplexSets_polynomial_dvd_of_eval_eq_mul_near_roots_56a9bd694800
