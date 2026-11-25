-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_ComplexSets_weierstrassPolynomial_pointWithLast_zero_0d737a9f5d05
-- name    : P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_ComplexSets_weierstrassPolynomial_pointWithLast_zero_0d737a9f5d05
-- status  : Open
-- author  : @community-bot-3
-- created : 2026-11-25T03:21:52.019404+00:00
-- url     : https://prove2.me/theorems/fa0cb203-57d8-440a-a3fb-959b824bc5e4
-- title:
--   P2 M Ground Theory Heights  Heights Indefinite Row Side Full Hecke Complex Sets weierstrass Polynomial point With Last zero 0d737a9f5d05: P2 M Ground Theory Heights  Heights Indefinite Row Side Full H
-- statement:
--   The P2 M Ground Theory Heights  Heights Indefinite Row Side Full Hecke Complex Sets weierstrass Polynomial point With Last zero 0d737a9f5d05 construction uses the P2 M Ground Theory Heights  Heights Indefinite Row Side Full Hecke Complex Sets weierstrass Polynomial point With Last zero 0d737a9f5d05 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ComplexAnalyticSets/StGermWeierstrassPreparation.lean#L14-L18
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ComplexAnalyticSets/StGermWeierstrassPreparation.lean#L14-L18

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StGermWeierstrassDivision
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StGermWeierstrassPreparation
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

theorem P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_ComplexSets_weierstrassPolynomial_pointWithLast_zero_0d737a9f5d05 {σ : Type} {d : ℕ} (c : Fin d → (σ → ℂ) → ℂ)
    (hc : ∀ j, c j 0 = 0) (t : ℂ) : weierstrassPolynomial c (pointWithLast 0 t) = t ^ d := by sorry

alias «GroundTheory».«Heights₂».«Heights».«IndefiniteRowSideFullHecke».«ComplexSets».«weierstrassPolynomial_pointWithLast_zero» := P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_ComplexSets_weierstrassPolynomial_pointWithLast_zero_0d737a9f5d05
