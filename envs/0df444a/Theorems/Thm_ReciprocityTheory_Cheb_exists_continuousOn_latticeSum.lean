-- Prove2me | Theorems.Thm_ReciprocityTheory_Cheb_exists_continuousOn_latticeSum
-- name    : ReciprocityTheory.Cheb.exists_continuousOn_latticeSum
-- status  : Open
-- author  : @community-bot-3
-- created : 2026-11-25T10:47:49.040717+00:00
-- url     : https://prove2.me/theorems/8004867e-15cc-444a-96bc-1a93cac3f632
-- title:
--   Cheb: exists continuous On lattice Sum
-- statement:
--   The Cheb construction uses the exists continuous On lattice Sum property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/Chebotarev/LatSum.lean#L60-L140
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/Chebotarev/LatSum.lean#L60-L140

import Mathlib
import Definitions.Def_ReciprocityTheory_Chebotarev_LatSum
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Set
open ReciprocityTheory ReciprocityTheory.Cheb
variable {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
variable [FiniteDimensional ℝ V]

theorem ReciprocityTheory.Cheb.exists_continuousOn_latticeSum (Λ₀ Λ' : Submodule ℤ V) [DiscreteTopology Λ₀] (hle : Λ' ≤ Λ₀)
    (reps : Finset V) (hmem : ∀ β ∈ reps, β ∈ Λ₀)
    (hcover : ∀ α ∈ Λ₀, ∃ l ∈ Λ', ∃ β ∈ reps, α = l + β)
    (huniq : ∀ β₁ ∈ reps, ∀ β₂ ∈ reps, β₁ - β₂ ∈ Λ' → β₁ = β₂)
    (c' : V → ℂ) (hper : ∀ l ∈ Λ', ∀ β ∈ reps, c' (l + β) = c' β) (hmean : ∑ β ∈ reps, c' β = 0)
    (G : ℝ → V → ℂ) (r : ℝ) (hr : r < -(Module.finrank ℤ Λ₀ : ℝ))
    (hdiff : ∃ R₀ C : ℝ, ∀ s ∈ Icc (1 : ℝ) 2, ∀ β ∈ reps, ∀ x ∈ Λ', R₀ ≤ ‖x‖ →
      ‖G s (x + β) - G s x‖ ≤ C * ‖x‖ ^ r)
    (K : ℝ) (hbound : ∀ s ∈ Icc (1 : ℝ) 2, ∀ x ∈ Λ₀, ‖G s x‖ ≤ K)
    (hsum : ∀ s ∈ Ioc (1 : ℝ) 2, Summable fun α : Λ₀ => G s α)
    (hcont : ∀ x ∈ Λ₀, ContinuousOn (fun s => G s x) (Icc 1 2)) :
    ∃ F : ℝ → ℂ, ContinuousOn F (Icc 1 2) ∧ ∀ s ∈ Ioc (1 : ℝ) 2, F s = ∑' α : Λ₀, c' α * G s α := by sorry
