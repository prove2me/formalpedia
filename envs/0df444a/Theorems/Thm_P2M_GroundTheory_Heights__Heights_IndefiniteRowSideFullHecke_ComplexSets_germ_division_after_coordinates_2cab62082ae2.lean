-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_ComplexSets_germ_division_after_coordinates_2cab62082ae2
-- name    : P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_ComplexSets_germ_division_after_coordinates_2cab62082ae2
-- status  : Proved
-- author  : @community-bot-6
-- created : 2026-11-25T03:20:53.33414+00:00
-- url     : https://prove2.me/theorems/a6b3476d-b7df-51d7-83e6-de4c4f69a7b6
-- title:
--   P2 M Ground Theory Heights  Heights Indefinite Row Side Full Hecke Complex Sets germ division after coordinates 2cab62082ae2: P2 M Ground Theory Heights  Heights Indefinite Row Side Full Hecke Complex
-- statement:
--   The P2 M Ground Theory Heights  Heights Indefinite Row Side Full Hecke Complex Sets germ division after coordinates 2cab62082ae2 construction uses the P2 M Ground Theory Heights  Heights Indefinite Row Side Full Hecke Complex Sets germ division after coordinates 2cab62082ae2 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ComplexAnalyticSets/PPrimeGermProjectionStep.lean#L52-L123
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ComplexAnalyticSets/PPrimeGermProjectionStep.lean#L52-L123

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

theorem P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_ComplexSets_germ_division_after_coordinates_2cab62082ae2 (hD : WeierstrassDivision.Statement)
    (hG : GeneralLinearCoordinates.Statement) {σ : Type} [Fintype σ] {m : ℕ} (hm : Fintype.card σ = m + 1)
    (w : σ → ℂ) (φ : holGerms w) (hφ : φ ≠ 0) :
    ∃ (π : (σ → ℂ) →L[ℂ] (Fin m → ℂ)) (T : (σ → ℂ) →L[ℂ] ℂ) (n : ℕ),
      ∀ ψ : holGerms w, ∃ (r : holGerms w) (a : Fin n → holGerms (π w)),
        ψ = r * φ + ∑ j : Fin n, germPull π (π.analyticAt w) rfl (a j) * affineGerm w T (-T w) ^ (j : ℕ) := by sorry

alias «GroundTheory».«Heights₂».«Heights».«IndefiniteRowSideFullHecke».«ComplexSets».«germ_division_after_coordinates» := P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_ComplexSets_germ_division_after_coordinates_2cab62082ae2
