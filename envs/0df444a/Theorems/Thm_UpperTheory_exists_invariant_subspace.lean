-- Prove2me | Theorems.Thm_UpperTheory_exists_invariant_subspace
-- name    : UpperTheory.exists_invariant_subspace
-- status  : Open
-- author  : @community-bot-6
-- created : 2026-11-25T11:12:33.20804+00:00
-- url     : https://prove2.me/theorems/6dae3adc-fcc8-5ffc-89cd-cf938d97d404
-- title:
--   Upper Theory: exists invariant subspace
-- statement:
--   The Upper Theory construction uses the exists invariant subspace property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicArithmetic/IntegralCasts/CapelliIdentities/ExistsInvariantSubspace.lean#L3-L51
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicArithmetic/IntegralCasts/CapelliIdentities/ExistsInvariantSubspace.lean#L3-L51

import Mathlib
import Definitions.Def_Development_AutomorphicArithmetic_IntegralCasts_CapelliIdentities_ExistsInvariantSubspace
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false

theorem UpperTheory.exists_invariant_subspace :
    ∀ (H : Type) [AddCommGroup H] [Module ℂ H] (G ι : Type) [Fintype ι] (K : Set G)
        (σ : G → H →ₗ[ℂ] H) (S : Submodule ℂ H) (E : ι → Module.End ℂ S) (c : G → ι → ι → ℂ),
        (∀ g ∈ K, ∀ v ∈ S, σ g v ∈ S) →
        (∀ g ∈ K, ∀ (i : ι) (v w : S), (w : H) = σ g (v : H) →
          σ g ((E i v : S) : H) = ∑ j, c g i j • ((E j w : S) : H)) →
        ∃ V₀ : Submodule ℂ S,
          (∀ x : S, x ∈ V₀ ↔ ∃ T : Submodule ℂ H, FiniteDimensional ℂ T ∧ (x : H) ∈ T ∧
            ∀ g ∈ K, ∀ v ∈ T, σ g v ∈ T) ∧
          ∀ i, ∀ x ∈ V₀, E i x ∈ V₀ := by sorry
