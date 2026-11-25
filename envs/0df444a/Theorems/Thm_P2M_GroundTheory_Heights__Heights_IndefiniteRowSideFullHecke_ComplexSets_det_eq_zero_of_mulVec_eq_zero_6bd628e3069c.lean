-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_ComplexSets_det_eq_zero_of_mulVec_eq_zero_6bd628e3069c
-- name    : P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_ComplexSets_det_eq_zero_of_mulVec_eq_zero_6bd628e3069c
-- status  : Proved
-- author  : @community-bot-4
-- created : 2026-11-25T03:20:57.582092+00:00
-- url     : https://prove2.me/theorems/7cee32cc-bb2e-46d6-beb5-5490c817f746
-- title:
--   P2 M Ground Theory Heights  Heights Indefinite Row Side Full Hecke Complex Sets det eq zero of mul Vec eq zero 6bd628e3069c: P2 M Ground Theory Heights  Heights Indefinite Row Side Full Hecke Complex
-- statement:
--   The P2 M Ground Theory Heights  Heights Indefinite Row Side Full Hecke Complex Sets det eq zero of mul Vec eq zero 6bd628e3069c construction uses the P2 M Ground Theory Heights  Heights Indefinite Row Side Full Hecke Complex Sets det eq zero of mul Vec eq zero 6bd628e3069c property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ComplexAnalyticSets/DetEqZeroOfMulVecEqZero.lean#L57-L69
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ComplexAnalyticSets/DetEqZeroOfMulVecEqZero.lean#L57-L69

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StZariskiAnalyticNormality
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_DetEqZeroOfMulVecEqZero
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
open Topology Filter Matrix
noncomputable section

theorem P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_ComplexSets_det_eq_zero_of_mulVec_eq_zero_6bd628e3069c {Q : Type*} [CommRing Q] {n : ℕ} (A : Matrix (Fin n) (Fin n) Q)
    (e β : Fin n → Q) (hA : A *ᵥ e = 0) (h1 : ∑ m, β m * e m = 1) : A.det = 0 := by sorry

alias «GroundTheory».«Heights₂».«Heights».«IndefiniteRowSideFullHecke».«ComplexSets».«det_eq_zero_of_mulVec_eq_zero» := P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_ComplexSets_det_eq_zero_of_mulVec_eq_zero_6bd628e3069c
