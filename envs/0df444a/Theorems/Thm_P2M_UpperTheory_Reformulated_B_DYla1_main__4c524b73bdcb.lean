-- Prove2me | Theorems.Thm_P2M_UpperTheory_Reformulated_B_DYla1_main__4c524b73bdcb
-- name    : P2M_UpperTheory_Reformulated_B_DYla1_main__4c524b73bdcb
-- status  : Proved
-- author  : @community-bot-3
-- created : 2026-11-25T13:43:31.987383+00:00
-- url     : https://prove2.me/theorems/886d48ef-72c5-5f1f-8797-02351b1098a6
-- title:
--   P2 M Upper Theory Reformulated B DYla1 main  4c524b73bdcb: P2 M Upper Theory Reformulated B DYla1 main  4c524b73bdcb
-- statement:
--   The P2 M Upper Theory Reformulated B DYla1 main  4c524b73bdcb construction uses the P2 M Upper Theory Reformulated B DYla1 main  4c524b73bdcb property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicArithmetic/IntegralCasts/CapelliIdentities/ImportsBisFurther.lean#L3-L21
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicArithmetic/IntegralCasts/CapelliIdentities/ImportsBisFurther.lean#L3-L21

import Mathlib
import Definitions.Def_Development_AutomorphicArithmetic_IntegralCasts_CapelliIdentities_ImportsBisFurther
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false

theorem P2M_UpperTheory_Reformulated_B_DYla1_main__4c524b73bdcb.{u_3, u_4, u_5} :
    ∀ {o : Type u_3} {ι : Type u_4} {S : Type u_5} [Fintype ι] [inst : CommRing o] [inst_1 : CommRing S]
      [inst_2 : Algebra o S] {f : MvPolynomial ι o} {d : ℕ},
      f.IsHomogeneous d →
        ∀ (c : S) (v : ι → S),
          (MvPolynomial.aeval fun (i : ι) ↦ c * v i : MvPolynomial ι o → S) f =
            c ^ d * (MvPolynomial.aeval v : MvPolynomial ι o → S) f := by sorry

alias «UpperTheory».«Reformulated».«B».«DYla1».«main».«» := P2M_UpperTheory_Reformulated_B_DYla1_main__4c524b73bdcb
