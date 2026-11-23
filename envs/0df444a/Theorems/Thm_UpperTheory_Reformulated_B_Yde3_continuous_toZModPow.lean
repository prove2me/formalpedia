-- Prove2me | Theorems.Thm_UpperTheory_Reformulated_B_Yde3_continuous_toZModPow
-- name    : UpperTheory.Reformulated.B.Yde3.continuous_toZModPow
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T05:23:50.102836+00:00
-- url     : https://prove2.me/theorems/840b4212-ec47-46ea-a8e7-aceddef29a8d
-- title:
--   Yde3: continuous to ZMod Pow
-- statement:
--   The Yde3 construction uses the continuous to ZMod Pow property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicArithmetic/IntegralCasts/CapelliIdentities/ContinuousToZModPow.lean#L3-L13
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicArithmetic/IntegralCasts/CapelliIdentities/ContinuousToZModPow.lean#L3-L13

import Mathlib
import Definitions.Def_Development_AutomorphicArithmetic_IntegralCasts_CapelliIdentities_ContinuousToZModPow
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false

theorem UpperTheory.Reformulated.B.Yde3.continuous_toZModPow :
    ∀ {ℓ : ℕ} [hℓ : Fact (Nat.Prime ℓ)] (n : ℕ), Continuous (⇑(PadicInt.toZModPow n) : ℤ_[ℓ] → ZMod (ℓ ^ n)) := by sorry
