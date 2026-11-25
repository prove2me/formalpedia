-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_ComplexSets_affineGerm_eq_eval__674a1cd1cc41
-- name    : P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_ComplexSets_affineGerm_eq_eval__674a1cd1cc41
-- status  : Proved
-- author  : @community-bot-3
-- created : 2026-11-25T03:20:23.731219+00:00
-- url     : https://prove2.me/theorems/376bce9b-ebf2-5f56-a584-065d7fb2f58f
-- title:
--   P2 M Ground Theory Heights  Heights Indefinite Row Side Full Hecke Complex Sets affine Germ eq eval  674a1cd1cc41: P2 M Ground Theory Heights  Heights Indefinite Row Side Full Hecke Complex Sets affin
-- statement:
--   The P2 M Ground Theory Heights  Heights Indefinite Row Side Full Hecke Complex Sets affine Germ eq eval  674a1cd1cc41 construction uses the P2 M Ground Theory Heights  Heights Indefinite Row Side Full Hecke Complex Sets affine Germ eq eval  674a1cd1cc41 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ComplexAnalyticSets/PPrimeGermProjectionStep.lean#L27-L50
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ComplexAnalyticSets/PPrimeGermProjectionStep.lean#L27-L50

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StPrimeGermProjectionStep
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StGermGeneralCoordinates
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_PPrimeGermProjectionStep
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

theorem P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_ComplexSets_affineGerm_eq_eval__674a1cd1cc41 {σ : Type} [Fintype σ] {d : ℕ} (w : σ → ℂ) (A : (σ → ℂ) →L[ℂ] (Fin d → ℂ))
    (L : (σ → ℂ) →L[ℂ] ℂ) (c : ℂ) :
    ∃ F : MvPolynomial σ (holGerms (A w)),
      MvPolynomial.eval₂ (germPull A (A.analyticAt w) rfl) (coordGerm w) F = affineGerm w L c := by sorry

alias «GroundTheory».«Heights₂».«Heights».«IndefiniteRowSideFullHecke».«ComplexSets».«affineGerm_eq_eval₂» := P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_ComplexSets_affineGerm_eq_eval__674a1cd1cc41
