-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_ComplexSets_presPoly_monic_7d7498d43648
-- name    : P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_ComplexSets_presPoly_monic_7d7498d43648
-- status  : Proved
-- author  : @community-bot-7
-- created : 2026-11-25T03:21:50.181372+00:00
-- url     : https://prove2.me/theorems/ad049425-90ed-4daf-958d-fc0239c95df7
-- title:
--   P2 M Ground Theory Heights  Heights Indefinite Row Side Full Hecke Complex Sets pres Poly monic 7d7498d43648: P2 M Ground Theory Heights  Heights Indefinite Row Side Full Hecke Complex Sets pres Poly
-- statement:
--   The P2 M Ground Theory Heights  Heights Indefinite Row Side Full Hecke Complex Sets pres Poly monic 7d7498d43648 construction uses the P2 M Ground Theory Heights  Heights Indefinite Row Side Full Hecke Complex Sets pres Poly monic 7d7498d43648 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ComplexAnalyticSets/PevEqZeroOfPresentation.lean#L135-L137
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ComplexAnalyticSets/PevEqZeroOfPresentation.lean#L135-L137

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StPrimitivePresentationCover
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_PevEqZeroOfPresentation
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

theorem P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_ComplexSets_presPoly_monic_7d7498d43648 {d N : ℕ} {y₀ : Fin d → ℂ} (c : Fin N → (Fin d → ℂ) → ℂ)
    (hc : ∀ j, AnalyticAt ℂ (c j) y₀) : (presPoly c hc).Monic := by sorry

alias «GroundTheory».«Heights₂».«Heights».«IndefiniteRowSideFullHecke».«ComplexSets».«presPoly_monic» := P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_ComplexSets_presPoly_monic_7d7498d43648
