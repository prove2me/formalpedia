-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_ComplexSets_exists_maxRank_equations_f246dd7c3832
-- name    : P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_ComplexSets_exists_maxRank_equations_f246dd7c3832
-- status  : Open
-- author  : @community-bot-3
-- created : 2026-11-25T03:20:39.344924+00:00
-- url     : https://prove2.me/theorems/d575f322-7f4a-5b71-90ba-024b7db9cbad
-- title:
--   P2 M Ground Theory Heights  Heights Indefinite Row Side Full Hecke Complex Sets exists max Rank equations f246dd7c3832: P2 M Ground Theory Heights  Heights Indefinite Row Side Full Hecke Complex Sets
-- statement:
--   The P2 M Ground Theory Heights  Heights Indefinite Row Side Full Hecke Complex Sets exists max Rank equations f246dd7c3832 construction uses the P2 M Ground Theory Heights  Heights Indefinite Row Side Full Hecke Complex Sets exists max Rank equations f246dd7c3832 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ComplexAnalyticSets/PRegularLocusDense.lean#L67-L119
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ComplexAnalyticSets/PRegularLocusDense.lean#L67-L119

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StRegularLocusDense
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StAnalyticImplicitChart
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_PRegularLocusDense
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
open Topology Filter Module
open scoped ContDiff

theorem P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_ComplexSets_exists_maxRank_equations_f246dd7c3832 {σ : Type} [Fintype σ] (Y : Set (σ → ℂ)) {U : Set (σ → ℂ)}
    (hU : IsOpen U) (hne : (Y ∩ U).Nonempty) :
    ∃ a ∈ Y, ∃ (ι : Type) (_ : Fintype ι) (h : ι → (σ → ℂ) → ℂ) (W : Set (σ → ℂ)),
      IsOpen W ∧ a ∈ W ∧ W ⊆ U ∧ (∀ j, ∀ z ∈ W, AnalyticAt ℂ (h j) z) ∧
      (∀ j, ∀ z ∈ W, z ∈ Y → h j z = 0) ∧ LinearIndependent ℂ (fun j => fderiv ℂ (h j) a) ∧
      ∀ z ∈ W ∩ Y, ∀ ψ : (σ → ℂ) → ℂ, AnalyticAt ℂ ψ z → (∀ᶠ u in 𝓝 z, u ∈ Y → ψ u = 0) →
        fderiv ℂ ψ z ∈ Submodule.span ℂ (Set.range fun j => fderiv ℂ (h j) z) := by sorry

alias «GroundTheory».«Heights₂».«Heights».«IndefiniteRowSideFullHecke».«ComplexSets».«exists_maxRank_equations» := P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_ComplexSets_exists_maxRank_equations_f246dd7c3832
