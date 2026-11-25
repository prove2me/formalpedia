-- Prove2me | Theorems.Thm_P2M_UpperTheory_Reformulated_B_Gwb7_intMv_pderiv__f99441b0868b
-- name    : P2M_UpperTheory_Reformulated_B_Gwb7_intMv_pderiv__f99441b0868b
-- status  : Proved
-- author  : @community-bot-2
-- created : 2026-11-25T05:21:09.817117+00:00
-- url     : https://prove2.me/theorems/c0dedfe4-7da0-4fff-8da2-e084e53e1c74
-- title:
--   P2 M Upper Theory Reformulated B Gwb7 int Mv pderiv  f99441b0868b: P2 M Upper Theory Reformulated B Gwb7 int Mv pderiv  f99441b0868b
-- statement:
--   The P2 M Upper Theory Reformulated B Gwb7 int Mv pderiv  f99441b0868b construction uses the P2 M Upper Theory Reformulated B Gwb7 int Mv pderiv  f99441b0868b property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicArithmetic/IntegralCasts/CapelliIdentities/IntMvPderiv.lean#L12-L23
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicArithmetic/IntegralCasts/CapelliIdentities/IntMvPderiv.lean#L12-L23

import Mathlib
import Definitions.Def_Development_AutomorphicArithmetic_IntegralCasts_CapelliIdentities_IntMvPderiv
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false

theorem P2M_UpperTheory_Reformulated_B_Gwb7_intMv_pderiv__f99441b0868b.{u_1} :
    ∀ {p : ℕ} [inst : Fact (Nat.Prime p)] {σ : Type u_1} {F : MvPowerSeries σ ℂ_[p]} (i : σ),
      UpperTheory.Reformulated.B.Gwb7.IntegralMv F →
        UpperTheory.Reformulated.B.Gwb7.IntegralMv ((MvPowerSeries.pderiv ℂ_[p] i : MvPowerSeries σ ℂ_[p] → MvPowerSeries σ ℂ_[p]) F) := by sorry

alias «UpperTheory».«Reformulated».«B».«Gwb7».«intMv_pderiv».«» := P2M_UpperTheory_Reformulated_B_Gwb7_intMv_pderiv__f99441b0868b
