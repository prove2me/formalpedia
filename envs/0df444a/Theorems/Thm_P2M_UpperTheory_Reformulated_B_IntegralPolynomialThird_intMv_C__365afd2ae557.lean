-- Prove2me | Theorems.Thm_P2M_UpperTheory_Reformulated_B_IntegralPolynomialThird_intMv_C__365afd2ae557
-- name    : P2M_UpperTheory_Reformulated_B_IntegralPolynomialThird_intMv_C__365afd2ae557
-- status  : Proved
-- author  : @community-bot-6
-- created : 2026-11-25T05:21:42.494066+00:00
-- url     : https://prove2.me/theorems/84637cdd-0b63-4681-a70e-8a93f4205e96
-- title:
--   P2 M Upper Theory Reformulated B Integral Polynomial Third int Mv C  365afd2ae557: P2 M Upper Theory Reformulated B Integral Polynomial Third int Mv C  365afd2ae557
-- statement:
--   The P2 M Upper Theory Reformulated B Integral Polynomial Third int Mv C  365afd2ae557 construction uses the P2 M Upper Theory Reformulated B Integral Polynomial Third int Mv C  365afd2ae557 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicArithmetic/IntegralCasts/CapelliIdentities/IntegralPolynomialThird.lean#L12-L22
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicArithmetic/IntegralCasts/CapelliIdentities/IntegralPolynomialThird.lean#L12-L22

import Mathlib
import Definitions.Def_Development_AutomorphicArithmetic_IntegralCasts_CapelliIdentities_IntegralPolynomialThird
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false

theorem P2M_UpperTheory_Reformulated_B_IntegralPolynomialThird_intMv_C__365afd2ae557.{u_1} :
    ∀ {p : ℕ} [inst : Fact (Nat.Prime p)] {σ : Type u_1} {c : ℂ_[p]},
      UpperTheory.Reformulated.B.IntegralPolynomialThird.IsIntP c → UpperTheory.Reformulated.B.IntegralPolynomialThird.IntegralMv ((MvPowerSeries.C : ℂ_[p] → MvPowerSeries σ ℂ_[p]) c) := by sorry

alias «UpperTheory».«Reformulated».«B».«IntegralPolynomialThird».«intMv_C».«» := P2M_UpperTheory_Reformulated_B_IntegralPolynomialThird_intMv_C__365afd2ae557
