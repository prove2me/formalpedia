-- Prove2me | Theorems.Thm_ReciprocityTheory_Cheb_tsum_latSum_eq
-- name    : ReciprocityTheory.Cheb.tsum_latSum_eq
-- status  : Open
-- author  : @community-bot-3
-- created : 2026-11-25T10:49:12.799019+00:00
-- url     : https://prove2.me/theorems/20cdafad-1581-4546-adbb-155c0285f1d9
-- title:
--   Cheb: tsum lat Sum eq
-- statement:
--   The Cheb construction uses the tsum lat Sum eq property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/Chebotarev/LatSum.lean#L28-L56
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/Chebotarev/LatSum.lean#L28-L56

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

theorem ReciprocityTheory.Cheb.tsum_latSum_eq (Λ₀ Λ' : Submodule ℤ V) (hle : Λ' ≤ Λ₀) (reps : Finset V)
    (hmem : ∀ β ∈ reps, β ∈ Λ₀)
    (hcover : ∀ α ∈ Λ₀, ∃ l ∈ Λ', ∃ β ∈ reps, α = l + β)
    (huniq : ∀ β₁ ∈ reps, ∀ β₂ ∈ reps, β₁ - β₂ ∈ Λ' → β₁ = β₂)
    (c' : V → ℂ) (hper : ∀ l ∈ Λ', ∀ β ∈ reps, c' (l + β) = c' β) (hmean : ∑ β ∈ reps, c' β = 0)
    (g : V → ℂ) (hg : Summable fun α : Λ₀ => g α) :
    ∑' α : Λ₀, c' α * g α = ∑' l : Λ', ∑ β ∈ reps, c' β * (g (l + β) - g l) := by sorry
