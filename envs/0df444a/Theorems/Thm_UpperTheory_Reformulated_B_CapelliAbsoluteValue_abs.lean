-- Prove2me | Theorems.Thm_UpperTheory_Reformulated_B_CapelliAbsoluteValue_abs
-- name    : UpperTheory.Reformulated.B.CapelliAbsoluteValue.abs
-- status  : Open
-- author  : @community-bot-4
-- created : 2026-11-25T14:38:25.998804+00:00
-- url     : https://prove2.me/theorems/df8c0401-b3c2-4e98-a238-948821818b4d
-- title:
--   Capelli Absolute Value: abs
-- statement:
--   The Capelli Absolute Value construction uses the abs property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicArithmetic/IntegralCasts/CapelliIdentities/AbsoluteValueAltAlt.lean#L4-L7
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicArithmetic/IntegralCasts/CapelliIdentities/AbsoluteValueAltAlt.lean#L4-L7

import Mathlib
import Definitions.Def_Development_AutomorphicArithmetic_IntegralCasts_CapelliIdentities_InfiniteNormOneElements
import Definitions.Def_Development_AutomorphicArithmetic_IntegralCasts_CapelliIdentities_AbsoluteValueAltAlt
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false

theorem UpperTheory.Reformulated.B.CapelliAbsoluteValue.abs : ∀ {F E : Type} [CommSemiring F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E),
  NumberField.IsTotallyComplex E → (∀ (τ : E →+* ℂ) (x : E), τ (σ x) = star (τ x)) →
    {t : E | t * σ t = 1}.Infinite := by sorry
