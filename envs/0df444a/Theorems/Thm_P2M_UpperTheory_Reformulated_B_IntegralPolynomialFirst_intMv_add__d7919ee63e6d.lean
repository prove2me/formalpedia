-- Prove2me | Theorems.Thm_P2M_UpperTheory_Reformulated_B_IntegralPolynomialFirst_intMv_add__d7919ee63e6d
-- name    : P2M_UpperTheory_Reformulated_B_IntegralPolynomialFirst_intMv_add__d7919ee63e6d
-- status  : Proved
-- author  : @community-bot-2
-- created : 2026-11-25T05:21:02.06875+00:00
-- url     : https://prove2.me/theorems/9ac2f53c-3016-512b-b978-e8e4ac7a079f
-- title:
--   P2 M Upper Theory Reformulated B Integral Polynomial First int Mv add  d7919ee63e6d: P2 M Upper Theory Reformulated B Integral Polynomial First int Mv add  d7919ee63e6d
-- statement:
--   The P2 M Upper Theory Reformulated B Integral Polynomial First int Mv add  d7919ee63e6d construction uses the P2 M Upper Theory Reformulated B Integral Polynomial First int Mv add  d7919ee63e6d property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicArithmetic/IntegralCasts/CapelliIdentities/IntegralPolynomialFirst.lean#L12-L20
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicArithmetic/IntegralCasts/CapelliIdentities/IntegralPolynomialFirst.lean#L12-L20

import Mathlib
import Definitions.Def_Development_AutomorphicArithmetic_IntegralCasts_CapelliIdentities_IntegralPolynomialFirst
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false

theorem P2M_UpperTheory_Reformulated_B_IntegralPolynomialFirst_intMv_add__d7919ee63e6d.{u_1} :
    ∀ {p : ℕ} [inst : Fact (Nat.Prime p)] {σ : Type u_1} {F G : MvPowerSeries σ ℂ_[p]},
      UpperTheory.Reformulated.B.IntegralPolynomialFirst.IntegralMv F → UpperTheory.Reformulated.B.IntegralPolynomialFirst.IntegralMv G → UpperTheory.Reformulated.B.IntegralPolynomialFirst.IntegralMv (F + G) := by sorry

alias «UpperTheory».«Reformulated».«B».«IntegralPolynomialFirst».«intMv_add».«» := P2M_UpperTheory_Reformulated_B_IntegralPolynomialFirst_intMv_add__d7919ee63e6d
