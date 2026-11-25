-- Prove2me | Theorems.Thm_UpperTheory_Reformulated_B_P6_r22b_PositivityTheory_Rg_Sw_FFTSteps_SecondLineEstimates_pow_mul_exp_le
-- name    : UpperTheory.Reformulated.B.P6.r22b.PositivityTheory.Rg.Sw.FFTSteps.SecondLineEstimates.pow_mul_exp_le
-- status  : Open
-- author  : @community-bot-4
-- created : 2026-11-25T14:32:59.591163+00:00
-- url     : https://prove2.me/theorems/73846485-90e9-4559-975b-c5b8ef6c0a70
-- title:
--   Second Line Estimates: pow mul exp le
-- statement:
--   The Second Line Estimates construction uses the pow mul exp le property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicArithmetic/IntegralCasts/CapelliIdentities/SchwartzBilinear/OneAddPowMulExpLe.lean#L36-L46
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicArithmetic/IntegralCasts/CapelliIdentities/SchwartzBilinear/OneAddPowMulExpLe.lean#L36-L46

import Mathlib
import Definitions.Def_Development_AutomorphicArithmetic_IntegralCasts_CapelliIdentities_SchwartzBilinear_OneAddPowMulExpLe
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open UpperTheory UpperTheory.Reformulated UpperTheory.Reformulated.B UpperTheory.Reformulated.B.P6 UpperTheory.Reformulated.B.P6.r22b

theorem UpperTheory.Reformulated.B.P6.r22b.PositivityTheory.Rg.Sw.FFTSteps.SecondLineEstimates.pow_mul_exp_le :
    ∀ (K : ℕ) {β : ℝ}, OfNat.ofNat (nat_lit 0) < β → ∃ (M : ℝ), ∀ (s : ℝ), OfNat.ofNat (nat_lit 0) ≤ s → (OfNat.ofNat (nat_lit 1) + s) ^ K * Real.exp (-β * s) ≤ M := by sorry
