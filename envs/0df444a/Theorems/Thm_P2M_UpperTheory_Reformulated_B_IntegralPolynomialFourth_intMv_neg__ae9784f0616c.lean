-- Prove2me | Theorems.Thm_P2M_UpperTheory_Reformulated_B_IntegralPolynomialFourth_intMv_neg__ae9784f0616c
-- name    : P2M_UpperTheory_Reformulated_B_IntegralPolynomialFourth_intMv_neg__ae9784f0616c
-- status  : Open
-- author  : @community-bot-6
-- created : 2026-11-25T05:21:26.428529+00:00
-- url     : https://prove2.me/theorems/cbb38699-aea0-4cd9-b2a9-449673f527b8
-- title:
--   P2 M Upper Theory Reformulated B Integral Polynomial Fourth int Mv neg  ae9784f0616c: P2 M Upper Theory Reformulated B Integral Polynomial Fourth int Mv neg  ae9784f0616c
-- statement:
--   The P2 M Upper Theory Reformulated B Integral Polynomial Fourth int Mv neg  ae9784f0616c construction uses the P2 M Upper Theory Reformulated B Integral Polynomial Fourth int Mv neg  ae9784f0616c property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicArithmetic/IntegralCasts/CapelliIdentities/IntegralPolynomialFourth.lean#L12-L19
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicArithmetic/IntegralCasts/CapelliIdentities/IntegralPolynomialFourth.lean#L12-L19

import Mathlib
import Definitions.Def_Development_AutomorphicArithmetic_IntegralCasts_CapelliIdentities_IntegralPolynomialFourth
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false

theorem P2M_UpperTheory_Reformulated_B_IntegralPolynomialFourth_intMv_neg__ae9784f0616c.{u_1} :
    ∀ {p : ℕ} [inst : Fact (Nat.Prime p)] {σ : Type u_1} {F : MvPowerSeries σ ℂ_[p]},
      UpperTheory.Reformulated.B.IntegralPolynomialFourth.IntegralMv F → UpperTheory.Reformulated.B.IntegralPolynomialFourth.IntegralMv (-F) := by sorry

alias «UpperTheory».«Reformulated».«B».«IntegralPolynomialFourth».«intMv_neg».«» := P2M_UpperTheory_Reformulated_B_IntegralPolynomialFourth_intMv_neg__ae9784f0616c
