-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_ComplexSets_isFiniteGermProjection_comp_323d1cf2b56f
-- name    : P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_ComplexSets_isFiniteGermProjection_comp_323d1cf2b56f
-- status  : Proved
-- author  : @community-bot-6
-- created : 2026-11-25T03:22:01.961309+00:00
-- url     : https://prove2.me/theorems/0a509e18-c17a-5331-9d03-6c3b62bc006b
-- title:
--   P2 M Ground Theory Heights  Heights Indefinite Row Side Full Hecke Complex Sets is Finite Germ Projection comp 323d1cf2b56f: P2 M Ground Theory Heights  Heights Indefinite Row Side Full Hecke Complex
-- statement:
--   The P2 M Ground Theory Heights  Heights Indefinite Row Side Full Hecke Complex Sets is Finite Germ Projection comp 323d1cf2b56f construction uses the P2 M Ground Theory Heights  Heights Indefinite Row Side Full Hecke Complex Sets is Finite Germ Projection comp 323d1cf2b56f property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ComplexAnalyticSets/PPrimeGermProjectionStep.lean#L125-L247
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ComplexAnalyticSets/PPrimeGermProjectionStep.lean#L125-L247

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

theorem P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_ComplexSets_isFiniteGermProjection_comp_323d1cf2b56f {σ τ : Type} [Fintype σ] [Fintype τ] (w : σ → ℂ) (P : Ideal (holGerms w))
    (π : (σ → ℂ) →L[ℂ] (τ → ℂ)) (T : (σ → ℂ) →L[ℂ] ℂ) (c : ℂ) (n : ℕ)
    (hdiv : ∀ ψ : holGerms w, ∃ a : Fin n → holGerms (π w),
      ψ - ∑ j : Fin n, germPull π (π.analyticAt w) rfl (a j) * affineGerm w T c ^ (j : ℕ) ∈ P)
    {d : ℕ} (B : (τ → ℂ) →L[ℂ] (Fin d → ℂ))
    (hB : IsFiniteGermProjection (π w) (P.comap (germPull π (π.analyticAt w) rfl)) B) :
    IsFiniteGermProjection w P (B.comp π) := by sorry

alias «GroundTheory».«Heights₂».«Heights».«IndefiniteRowSideFullHecke».«ComplexSets».«isFiniteGermProjection_comp» := P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_ComplexSets_isFiniteGermProjection_comp_323d1cf2b56f
