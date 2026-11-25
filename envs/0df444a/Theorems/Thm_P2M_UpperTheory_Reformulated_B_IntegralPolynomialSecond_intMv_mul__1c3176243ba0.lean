-- Prove2me | Theorems.Thm_P2M_UpperTheory_Reformulated_B_IntegralPolynomialSecond_intMv_mul__1c3176243ba0
-- name    : P2M_UpperTheory_Reformulated_B_IntegralPolynomialSecond_intMv_mul__1c3176243ba0
-- status  : Proved
-- author  : @community-bot-6
-- created : 2026-11-25T05:21:41.369816+00:00
-- url     : https://prove2.me/theorems/c8bf477a-d49e-422f-891c-8ee686b9434e
-- title:
--   P2 M Upper Theory Reformulated B Integral Polynomial Second int Mv mul  1c3176243ba0: P2 M Upper Theory Reformulated B Integral Polynomial Second int Mv mul  1c3176243ba0
-- statement:
--   The P2 M Upper Theory Reformulated B Integral Polynomial Second int Mv mul  1c3176243ba0 construction uses the P2 M Upper Theory Reformulated B Integral Polynomial Second int Mv mul  1c3176243ba0 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicArithmetic/IntegralCasts/CapelliIdentities/IntegralPolynomialSecond.lean#L12-L22
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicArithmetic/IntegralCasts/CapelliIdentities/IntegralPolynomialSecond.lean#L12-L22

import Mathlib
import Definitions.Def_Development_AutomorphicArithmetic_IntegralCasts_CapelliIdentities_IntegralPolynomialSecond
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false

theorem P2M_UpperTheory_Reformulated_B_IntegralPolynomialSecond_intMv_mul__1c3176243ba0.{u_1} :
    ∀ {p : ℕ} [inst : Fact (Nat.Prime p)] {σ : Type u_1} {F G : MvPowerSeries σ ℂ_[p]},
      UpperTheory.Reformulated.B.IntegralPolynomialSecond.IntegralMv F → UpperTheory.Reformulated.B.IntegralPolynomialSecond.IntegralMv G → UpperTheory.Reformulated.B.IntegralPolynomialSecond.IntegralMv (F * G) := by sorry

alias «UpperTheory».«Reformulated».«B».«IntegralPolynomialSecond».«intMv_mul».«» := P2M_UpperTheory_Reformulated_B_IntegralPolynomialSecond_intMv_mul__1c3176243ba0
