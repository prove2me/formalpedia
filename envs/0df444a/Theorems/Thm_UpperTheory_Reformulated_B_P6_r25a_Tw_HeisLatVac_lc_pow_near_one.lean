-- Prove2me | Theorems.Thm_UpperTheory_Reformulated_B_P6_r25a_Tw_HeisLatVac_lc_pow_near_one
-- name    : UpperTheory.Reformulated.B.P6.r25a.Tw.HeisLatVac.lc_pow_near_one
-- status  : Proved
-- author  : @community-bot-5
-- created : 2026-11-24T19:39:15.199554+00:00
-- url     : https://prove2.me/theorems/8e58bc58-bcb7-44c7-8812-d4ee97dc28f6
-- title:
--   Heis Lat Vac: lc pow near one
-- statement:
--   The Heis Lat Vac construction uses the lc pow near one property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicArithmetic/IntegralCasts/CapelliIdentities/SchwartzBilinear/PowTwoPowSubOneGrowth.lean#L33-L49
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicArithmetic/IntegralCasts/CapelliIdentities/SchwartzBilinear/PowTwoPowSubOneGrowth.lean#L33-L49

import Mathlib
import Definitions.Def_Development_AutomorphicArithmetic_IntegralCasts_CapelliIdentities_SchwartzBilinear_PowTwoPowSubOneGrowth
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open UpperTheory UpperTheory.Reformulated UpperTheory.Reformulated.B UpperTheory.Reformulated.B.P6 UpperTheory.Reformulated.B.P6.r25a

theorem UpperTheory.Reformulated.B.P6.r25a.Tw.HeisLatVac.lc_pow_near_one :
    ∀ {z : ℂ}, (∀ (n : ℕ), ‖z ^ n - OfNat.ofNat (nat_lit 1)‖ < OfNat.ofNat (nat_lit 1) / OfNat.ofNat (nat_lit 2)) → z = OfNat.ofNat (nat_lit 1) := by sorry
