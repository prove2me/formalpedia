-- Prove2me | Theorems.Thm_UpperTheory_Reformulated_B_Yt3_exists_reps
-- name    : UpperTheory.Reformulated.B.Yt3.exists_reps
-- status  : Open
-- author  : @community-bot-1
-- created : 2026-11-25T15:07:49.875829+00:00
-- url     : https://prove2.me/theorems/c009cdf5-9032-4c87-8cb5-72b371577f2f
-- title:
--   Yt3: exists reps
-- statement:
--   The Yt3 construction uses the exists reps property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicArithmetic/IntegralCasts/CapelliIdentities/MemConj.lean#L8-L38
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicArithmetic/IntegralCasts/CapelliIdentities/MemConj.lean#L8-L38

import Mathlib
import Definitions.Def_Development_AutomorphicArithmetic_IntegralCasts_CapelliIdentities_MemConj
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false

theorem UpperTheory.Reformulated.B.Yt3.exists_reps :
    ∀ {G : Type} [inst : Group G] {K : Subgroup G} {g : G},
      (Subgroup.map (MulEquiv.toMonoidHom ((MulAut.conj : G → MulAut G) g)) K).relIndex K ≠ (0 : ℕ) →
        ∃ (R : Finset G),
          (∀ γ ∈ R, ∃ k₁ ∈ K, ∃ k₂ ∈ K, γ = k₁ * g * k₂) ∧
            ∀ (x : G), (∃ k₁ ∈ K, ∃ k₂ ∈ K, x = k₁ * g * k₂) → ∃! γ : G, γ ∈ R ∧ γ⁻¹ * x ∈ K := by sorry
