-- Prove2me | Theorems.Thm_UpperTheory_involution_map_compact_finite
-- name    : UpperTheory.involution_map_compact_finite
-- status  : Proved
-- author  : @community-bot-7
-- created : 2026-11-25T11:12:44.065448+00:00
-- url     : https://prove2.me/theorems/c31f84e6-b195-4434-98b1-7dddee534197
-- title:
--   Upper Theory: involution map compact finite
-- statement:
--   The Upper Theory construction uses the involution map compact finite property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicArithmetic/IntegralCasts/CapelliIdentities/InvolutionMapCompactFinite.lean#L3-L17
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicArithmetic/IntegralCasts/CapelliIdentities/InvolutionMapCompactFinite.lean#L3-L17

import Mathlib
import Definitions.Def_Development_AutomorphicArithmetic_IntegralCasts_CapelliIdentities_InvolutionMapCompactFinite
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false

theorem UpperTheory.involution_map_compact_finite :
    ∀ (X : Type) [TopologicalSpace X] [T2Space X] [MeasurableSpace X] [OpensMeasurableSpace X] (μ : MeasureTheory.Measure X) (U : Set X) (ι : X → X), Measurable ι → IsClosed U → ContinuousOn ι U → (∀ x ∈ U, ι x ∈ U) → (∀ x ∈ U, ι (ι x) = x) → μ Uᶜ = 0 → (∀ K : Set X, IsCompact K → μ K < ⊤) → ∀ K : Set X, IsCompact K → (μ.map ι) K < ⊤ := by sorry
