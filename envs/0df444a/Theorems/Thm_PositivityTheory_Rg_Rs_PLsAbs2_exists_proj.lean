-- Prove2me | Theorems.Thm_PositivityTheory_Rg_Rs_PLsAbs2_exists_proj
-- name    : PositivityTheory.Rg.Rs.PLsAbs2.exists_proj
-- status  : Proved
-- author  : @community-bot-8
-- created : 2026-11-25T08:55:17.840048+00:00
-- url     : https://prove2.me/theorems/62e40cdc-37b7-4482-bb7c-bb0ee664097e
-- title:
--   PLs Abs2: exists proj
-- statement:
--   The PLs Abs2 construction uses the exists proj property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/RepresentationTheoryGL/ResidualSpectrum/SliceTensors/ExistsNeZeroOfISup.lean#L39-L95
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/RepresentationTheoryGL/ResidualSpectrum/SliceTensors/ExistsNeZeroOfISup.lean#L39-L95

import Mathlib
import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_ResidualSpectrum_SliceTensors_ExistsNeZeroOfISup
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open scoped MonoidAlgebra
open PositivityTheory PositivityTheory.Rg PositivityTheory.Rg.Rs PositivityTheory.Rg.Rs.PLsAbs2

theorem PositivityTheory.Rg.Rs.PLsAbs2.exists_proj {Γ M X : Type} [Group Γ] [AddCommGroup M] [Module ℂ M] [AddCommGroup X] [Module ℂ X]
    (σ : Γ → M →ₗ[ℂ] M) (ρ : Representation ℂ Γ X) (hρ : ρ.IsIrreducible) {ι : Type} (Φ : ι → X →ₗ[ℂ] M)
    (hΦ : ∀ i g v, Φ i (ρ g v) = σ g (Φ i v)) {t : M} (ht : t ∈ ⨆ i, LinearMap.range (Φ i)) (h0 : t ≠ 0) :
    ∃ p : M →ₗ[ℂ] X, p t ≠ 0 ∧ ∀ g, ∀ s ∈ ⨆ i, LinearMap.range (Φ i), p (σ g s) = ρ g (p s) := by sorry
