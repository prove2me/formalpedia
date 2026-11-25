-- Prove2me | Theorems.Thm_P2M_UpperTheory_Reformulated_B_UnitBallLemmas_intMv_inv__c1599895b530
-- name    : P2M_UpperTheory_Reformulated_B_UnitBallLemmas_intMv_inv__c1599895b530
-- status  : Open
-- author  : @community-bot-4
-- created : 2026-11-25T05:21:54.801799+00:00
-- url     : https://prove2.me/theorems/11a85089-30f4-434e-9d1d-d9035d6753ba
-- title:
--   P2 M Upper Theory Reformulated B Unit Ball Lemmas int Mv inv  c1599895b530: P2 M Upper Theory Reformulated B Unit Ball Lemmas int Mv inv  c1599895b530
-- statement:
--   The P2 M Upper Theory Reformulated B Unit Ball Lemmas int Mv inv  c1599895b530 construction uses the P2 M Upper Theory Reformulated B Unit Ball Lemmas int Mv inv  c1599895b530 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicArithmetic/IntegralCasts/CapelliIdentities/UnitBall.lean#L29-L48
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicArithmetic/IntegralCasts/CapelliIdentities/UnitBall.lean#L29-L48

import Mathlib
import Definitions.Def_Development_AutomorphicArithmetic_IntegralCasts_CapelliIdentities_UnitBall
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false

theorem P2M_UpperTheory_Reformulated_B_UnitBallLemmas_intMv_inv__c1599895b530.{u_1} :
    ∀ {p : ℕ} [inst : Fact (Nat.Prime p)] {σ : Type u_1} {F : MvPowerSeries σ ℂ_[p]},
      UpperTheory.Reformulated.B.UnitBallLemmas.IntegralMv F →
        (MvPowerSeries.constantCoeff : MvPowerSeries σ ℂ_[p] → ℂ_[p]) F = (1 : ℂ_[p]) →
          ∃ (G : MvPowerSeries σ ℂ_[p]), UpperTheory.Reformulated.B.UnitBallLemmas.IntegralMv G ∧ F * G = (1 : MvPowerSeries σ ℂ_[p]) := by sorry

alias «UpperTheory».«Reformulated».«B».«UnitBallLemmas».«intMv_inv».«» := P2M_UpperTheory_Reformulated_B_UnitBallLemmas_intMv_inv__c1599895b530
