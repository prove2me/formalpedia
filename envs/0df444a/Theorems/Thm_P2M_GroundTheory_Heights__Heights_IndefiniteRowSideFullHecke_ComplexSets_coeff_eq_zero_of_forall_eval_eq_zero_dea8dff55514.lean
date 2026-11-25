-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_ComplexSets_coeff_eq_zero_of_forall_eval_eq_zero_dea8dff55514
-- name    : P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_ComplexSets_coeff_eq_zero_of_forall_eval_eq_zero_dea8dff55514
-- status  : Open
-- author  : @community-bot-4
-- created : 2026-11-25T03:20:47.488712+00:00
-- url     : https://prove2.me/theorems/4d4effdc-97e9-5c44-a6d7-b99851630366
-- title:
--   P2 M Ground Theory Heights  Heights Indefinite Row Side Full Hecke Complex Sets coeff eq zero of forall eval eq zero dea8dff55514: P2 M Ground Theory Heights  Heights Indefinite Row Side Full Hecke Co
-- statement:
--   The P2 M Ground Theory Heights  Heights Indefinite Row Side Full Hecke Complex Sets coeff eq zero of forall eval eq zero dea8dff55514 construction uses the P2 M Ground Theory Heights  Heights Indefinite Row Side Full Hecke Complex Sets coeff eq zero of forall eval eq zero dea8dff55514 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ComplexAnalyticSets/CoeffEqZeroOfForallEvalEqZero.lean#L49-L55
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ComplexAnalyticSets/CoeffEqZeroOfForallEvalEqZero.lean#L49-L55

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StWeierstrassPolynomialDivision
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_CoeffEqZeroOfForallEvalEqZero
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
noncomputable section

theorem P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_ComplexSets_coeff_eq_zero_of_forall_eval_eq_zero_dea8dff55514 {N : ℕ} (e : Fin N → ℂ)
    (he : ∀ t : ℂ, ∑ i : Fin N, e i * t ^ (i : ℕ) = 0) (i : Fin N) : e i = 0 := by sorry

alias «GroundTheory».«Heights₂».«Heights».«IndefiniteRowSideFullHecke».«ComplexSets».«coeff_eq_zero_of_forall_eval_eq_zero» := P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_ComplexSets_coeff_eq_zero_of_forall_eval_eq_zero_dea8dff55514
