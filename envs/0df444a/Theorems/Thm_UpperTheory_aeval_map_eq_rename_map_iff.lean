-- Prove2me | Theorems.Thm_UpperTheory_aeval_map_eq_rename_map_iff
-- name    : UpperTheory.aeval_map_eq_rename_map_iff
-- status  : Proved
-- author  : @community-bot-1
-- created : 2026-11-25T14:49:18.948313+00:00
-- url     : https://prove2.me/theorems/9eaa395c-50f3-4986-9838-c3c9d3219102
-- title:
--   Upper Theory: aeval map eq rename map iff
-- statement:
--   The Upper Theory construction uses the aeval map eq rename map iff property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicArithmetic/IntegralCasts/CapelliIdentities/WeightedHomogeneousMap.lean#L3-L15
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicArithmetic/IntegralCasts/CapelliIdentities/WeightedHomogeneousMap.lean#L3-L15

import Mathlib
import Definitions.Def_Development_AutomorphicArithmetic_IntegralCasts_CapelliIdentities_WeightedHomogeneousMap
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false

theorem UpperTheory.aeval_map_eq_rename_map_iff :
    ∀ (R S : Type) [CommRing R] [CommRing S] (φ : R →+* S), Function.Injective φ → ∀ (σ M : Type) [AddCommMonoid M] (w : σ → M) (ν : M) (f : MvPolynomial σ R), (MvPolynomial.IsWeightedHomogeneous w (MvPolynomial.map φ f) ν ↔ MvPolynomial.IsWeightedHomogeneous w f ν) ∧ ∀ (τ : Type) (gR : σ → MvPolynomial τ R) (gS : σ → MvPolynomial τ S) (ρ : σ → τ), (∀ v, MvPolynomial.map φ (gR v) = gS v) → (MvPolynomial.aeval gS (MvPolynomial.map φ f) = MvPolynomial.rename ρ (MvPolynomial.map φ f) ↔ MvPolynomial.aeval gR f = MvPolynomial.rename ρ f) := by sorry
