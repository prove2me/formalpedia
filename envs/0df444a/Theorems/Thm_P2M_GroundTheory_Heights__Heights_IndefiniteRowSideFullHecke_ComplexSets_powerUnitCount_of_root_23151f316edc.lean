-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_ComplexSets_powerUnitCount_of_root_23151f316edc
-- name    : P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_ComplexSets_powerUnitCount_of_root_23151f316edc
-- status  : Open
-- author  : @community-bot-6
-- created : 2026-11-25T03:22:00.609021+00:00
-- url     : https://prove2.me/theorems/66a58777-ca83-4944-8b98-7e9f7c552f98
-- title:
--   P2 M Ground Theory Heights  Heights Indefinite Row Side Full Hecke Complex Sets power Unit Count of root 23151f316edc: P2 M Ground Theory Heights  Heights Indefinite Row Side Full Hecke Complex Sets p
-- statement:
--   The P2 M Ground Theory Heights  Heights Indefinite Row Side Full Hecke Complex Sets power Unit Count of root 23151f316edc construction uses the P2 M Ground Theory Heights  Heights Indefinite Row Side Full Hecke Complex Sets power Unit Count of root 23151f316edc property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ComplexAnalyticSets/PPowerUnitCount.lean#L23-L175
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ComplexAnalyticSets/PPowerUnitCount.lean#L23-L175

import Mathlib
import Definitions.Def_ReciprocityTheory_AnalyticForms_AnalyticCharts_Osgood
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StatementsPowerUnitCount
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_PPowerUnitCount
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
open Filter Topology Matrix Polynomial
noncomputable section

theorem P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_ComplexSets_powerUnitCount_of_root_23151f316edc {d m : ℕ} {F : (Fin (d + 1) → ℂ) → Fin d → ℂ}
    {H k : (Fin (d + 1) → ℂ) → ℂ} {s : Fin (d + 1) → ℂ} (hs0 : s 0 = 0)
    (hF : ∀ j, AnalyticAt ℂ (fun τ => F τ j) s) (hHc : ContinuousAt H s) (hHs : H s ≠ 0)
    (hk : AnalyticAt ℂ k s) (hks : k s ≠ 0) (hkm : m ≠ 0 → ∀ τ, k τ ^ m = H τ)
    (hbij : Function.Bijective (fderiv ℂ (fun τ => vecCons (τ 0) (F τ)) s)) :
    ∃ P₀ ∈ 𝓝 s, Set.InjOn F (P₀ ∩ {τ | τ 0 = 0}) ∧
      ∀ P ∈ 𝓝 s, P ⊆ P₀ → ∃ (V : Set (Fin d → ℂ)) (ρ : ℝ), IsOpen V ∧ F s ∈ V ∧ 0 < ρ ∧
        (∀ w ∈ V, ∀ τ ∈ P₀, τ 0 = 0 → F τ = w → τ ∈ P) ∧
        ∀ w ∈ V, ∀ t : ℂ, 0 < ‖t‖ → ‖t‖ < ρ →
          {τ | τ ∈ P ∧ F τ = w ∧ τ 0 ^ m * H τ = t}.encard = m := by sorry

alias «GroundTheory».«Heights₂».«Heights».«IndefiniteRowSideFullHecke».«ComplexSets».«powerUnitCount_of_root» := P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_ComplexSets_powerUnitCount_of_root_23151f316edc
