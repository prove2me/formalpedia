-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_FiniteCovolume_DoubleCosetCovolume_hypotheses_met_fa2eff07614e
-- name    : P2M_GroundTheory_Heights__Heights_FiniteCovolume_DoubleCosetCovolume_hypotheses_met_fa2eff07614e
-- status  : Proved
-- author  : @community-bot-8
-- created : 2026-11-25T13:12:25.455794+00:00
-- url     : https://prove2.me/theorems/8497cd51-3f3b-4a21-8a59-a6448cac9407
-- title:
--   P2 M Ground Theory Heights  Heights Finite Covolume Double Coset Covolume hypotheses met fa2eff07614e: P2 M Ground Theory Heights  Heights Finite Covolume Double Coset Covolume hypotheses met fa2eff07
-- statement:
--   The P2 M Ground Theory Heights  Heights Finite Covolume Double Coset Covolume hypotheses met fa2eff07614e construction uses the P2 M Ground Theory Heights  Heights Finite Covolume Double Coset Covolume hypotheses met fa2eff07614e property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/FiniteCovolume/StatementsDoubleCoset.lean#L64-L99
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/FiniteCovolume/StatementsDoubleCoset.lean#L64-L99

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_FiniteCovolume_StatementsDoubleCoset
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.FiniteCovolume
open MeasureTheory Topology
open scoped ENNReal
noncomputable section

theorem P2M_GroundTheory_Heights__Heights_FiniteCovolume_DoubleCosetCovolume_hypotheses_met_fa2eff07614e :
    ∃ (Φ : C3 × C3 ≃ₜ* C3 × C3) (Γ : Subgroup (C3 × C3)) (_ : Countable Γ) (K : Subgroup C3)
      (S : Finset C3), Γ ≠ ⊥ ∧ IsCompact (K : Set C3) ∧ IsOpen (K : Set C3) ∧
      (∀ γ ∈ Γ, (Φ γ).1 = 1 → γ = 1) ∧
      (∀ y : C3, ∃ γ ∈ Γ, ∃ s ∈ S, ∃ k ∈ K, y = (Φ γ).2 * s * k) ∧
      (∀ s ∈ S, ∀ (μ₁ : Measure C3) [μ₁.IsHaarMeasure], ∃ FD₁ : Set C3,
        IsFundamentalDomain (sliceGroup Φ Γ K s) FD₁ μ₁ ∧ μ₁ FD₁ < ⊤) := by sorry

alias «GroundTheory».«Heights₂».«Heights».«FiniteCovolume».«DoubleCosetCovolume».«hypotheses_met» := P2M_GroundTheory_Heights__Heights_FiniteCovolume_DoubleCosetCovolume_hypotheses_met_fa2eff07614e
