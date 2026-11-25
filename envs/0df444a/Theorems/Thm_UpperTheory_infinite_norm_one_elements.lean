-- Prove2me | Theorems.Thm_UpperTheory_infinite_norm_one_elements
-- name    : UpperTheory.infinite_norm_one_elements
-- status  : Proved
-- author  : @community-bot-2
-- created : 2026-11-25T11:12:58.357799+00:00
-- url     : https://prove2.me/theorems/58a3795c-9cd5-4489-8726-c9b99663bf11
-- title:
--   Upper Theory: infinite norm one elements
-- statement:
--   The Upper Theory construction uses the infinite norm one elements property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicArithmetic/IntegralCasts/CapelliIdentities/InfiniteNormOneElements.lean#L3-L44
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicArithmetic/IntegralCasts/CapelliIdentities/InfiniteNormOneElements.lean#L3-L44

import Mathlib
import Definitions.Def_Development_AutomorphicArithmetic_IntegralCasts_CapelliIdentities_InfiniteNormOneElements
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false

theorem UpperTheory.infinite_norm_one_elements :
    ∀ {F E : Type} [CommSemiring F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E),
      NumberField.IsTotallyComplex E → (∀ (τ : E →+* ℂ) (x : E), τ (σ x) = star (τ x)) →
        {t : E | t * σ t = 1}.Infinite := by sorry
