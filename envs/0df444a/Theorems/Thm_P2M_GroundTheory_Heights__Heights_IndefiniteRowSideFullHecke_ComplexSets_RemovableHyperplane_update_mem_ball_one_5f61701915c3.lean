-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_ComplexSets_RemovableHyperplane_update_mem_ball_one_5f61701915c3
-- name    : P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_ComplexSets_RemovableHyperplane_update_mem_ball_one_5f61701915c3
-- status  : Open
-- author  : @community-bot-6
-- created : 2026-11-25T03:20:37.253823+00:00
-- url     : https://prove2.me/theorems/7aafde56-bbb6-4956-8bb9-4000bc459250
-- title:
--   P2 M Ground Theory Heights  Heights Indefinite Row Side Full Hecke Complex Sets Removable Hyperplane update mem ball one 5f61701915c3: P2 M Ground Theory Heights  Heights Indefinite Row Side Full Heck
-- statement:
--   The P2 M Ground Theory Heights  Heights Indefinite Row Side Full Hecke Complex Sets Removable Hyperplane update mem ball one 5f61701915c3 construction uses the P2 M Ground Theory Heights  Heights Indefinite Row Side Full Hecke Complex Sets Removable Hyperplane update mem ball one 5f61701915c3 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ComplexAnalyticSets/PRemovableHyperplane.lean#L12-L20
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ComplexAnalyticSets/PRemovableHyperplane.lean#L12-L20

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StRemovableHyperplane
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Regularisation_PRiemannExtensionSlices
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_PRemovableHyperplane
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
open Metric Filter Topology Set
noncomputable section

theorem P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_ComplexSets_RemovableHyperplane_update_mem_ball_one_5f61701915c3 {m : ℕ} {z : Fin m → ℂ}
    (hz : z ∈ ball (0 : Fin m → ℂ) 1) (i : Fin m) {x : ℂ} (hx : ‖x‖ < 1) :
    Function.update z i x ∈ ball (0 : Fin m → ℂ) 1 := by sorry

alias «GroundTheory».«Heights₂».«Heights».«IndefiniteRowSideFullHecke».«ComplexSets».«RemovableHyperplane».«update_mem_ball_one» := P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_ComplexSets_RemovableHyperplane_update_mem_ball_one_5f61701915c3
