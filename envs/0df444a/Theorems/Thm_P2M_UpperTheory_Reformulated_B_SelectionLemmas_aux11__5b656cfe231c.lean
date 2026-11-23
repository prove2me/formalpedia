-- Prove2me | Theorems.Thm_P2M_UpperTheory_Reformulated_B_SelectionLemmas_aux11__5b656cfe231c
-- name    : P2M_UpperTheory_Reformulated_B_SelectionLemmas_aux11__5b656cfe231c
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T05:19:14.870805+00:00
-- url     : https://prove2.me/theorems/74a5dcf7-ddb6-4caa-abc8-d85e112df11f
-- title:
--   P2 M Upper Theory Reformulated B Selection Lemmas aux11  5b656cfe231c: P2 M Upper Theory Reformulated B Selection Lemmas aux11  5b656cfe231c
-- statement:
--   The P2 M Upper Theory Reformulated B Selection Lemmas aux11  5b656cfe231c construction uses the P2 M Upper Theory Reformulated B Selection Lemmas aux11  5b656cfe231c property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicArithmetic/IntegralCasts/CapelliIdentities/SelectionLemmas.lean#L2077-L2137
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicArithmetic/IntegralCasts/CapelliIdentities/SelectionLemmas.lean#L2077-L2137

import Mathlib
import Definitions.Def_Development_AutomorphicArithmetic_IntegralCasts_CapelliIdentities_SelectionLemmas
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false

theorem P2M_UpperTheory_Reformulated_B_SelectionLemmas_aux11__5b656cfe231c.{u_1, u_2} :
    ∀ {R : Type u_1} [inst : CommRing R] {W : Type u_2} [inst_1 : AddCommGroup W]
      [inst_2 :
        @_root_.Module R W (@CommSemiring.toSemiring R (@CommRing.toCommSemiring R inst))
          (@AddCommGroup.toAddCommMonoid W inst_1)]
      (S :
        @Submonoid R
          (@MulZeroOneClass.toMulOneClass R
            (@instMulZeroOneClassOfSemiring R (@CommSemiring.toSemiring R (@CommRing.toCommSemiring R inst)))))
      (L :
        @Submodule R W (@CommSemiring.toSemiring R (@CommRing.toCommSemiring R inst))
          (@AddCommGroup.toAddCommMonoid W inst_1) inst_2),
      ∃ (s : R),
        And
          (@Membership.mem R
            (@Submonoid R
              (@MulZeroOneClass.toMulOneClass R
                (@instMulZeroOneClassOfSemiring R (@CommSemiring.toSemiring R (@CommRing.toCommSemiring R inst)))))
            (@SetLike.instMembership
              (@Submonoid R
                (@MulZeroOneClass.toMulOneClass R
                  (@instMulZeroOneClassOfSemiring R (@CommSemiring.toSemiring R (@CommRing.toCommSemiring R inst)))))
              R
              (@Submonoid.instSetLike R
                (@MulZeroOneClass.toMulOneClass R
                  (@instMulZeroOneClassOfSemiring R (@CommSemiring.toSemiring R (@CommRing.toCommSemiring R inst))))))
            S s)
          (@Membership.mem W
            (@Submodule R W (@CommSemiring.toSemiring R (@CommRing.toCommSemiring R inst))
              (@AddCommGroup.toAddCommMonoid W inst_1) inst_2)
            (@SetLike.instMembership
              (@Submodule R W (@CommSemiring.toSemiring R (@CommRing.toCommSemiring R inst))
                (@AddCommGroup.toAddCommMonoid W inst_1) inst_2)
              W
              (@Submodule.setLike R W (@CommSemiring.toSemiring R (@CommRing.toCommSemiring R inst))
                (@AddCommGroup.toAddCommMonoid W inst_1) inst_2))
            L
            (@HSMul.hSMul R W W
              (@instHSMul R W
                (@SMulZeroClass.toSMul R W
                  (@AddZero.toZero W
                    (@AddZeroClass.toAddZero W
                      (@AddMonoid.toAddZeroClass W
                        (@SubNegMonoid.toAddMonoid W (@AddGroup.toSubNegMonoid W (@AddCommGroup.toAddGroup W inst_1))))))
                  (@DistribSMul.toSMulZeroClass R W
                    (@AddMonoid.toAddZeroClass W
                      (@SubNegMonoid.toAddMonoid W (@AddGroup.toSubNegMonoid W (@AddCommGroup.toAddGroup W inst_1))))
                    (@DistribMulAction.toDistribSMul R W
                      (@Semiring.toMonoid R (@CommSemiring.toSemiring R (@CommRing.toCommSemiring R inst)))
                      (@SubNegMonoid.toAddMonoid W (@AddGroup.toSubNegMonoid W (@AddCommGroup.toAddGroup W inst_1)))
                      (@Module.toDistribMulAction R W (@CommSemiring.toSemiring R (@CommRing.toCommSemiring R inst))
                        (@AddCommGroup.toAddCommMonoid W inst_1) inst_2)))))
              s
              (@OfNat.ofNat W (nat_lit 0)
                (@Zero.toOfNat0 W
                  (@AddZero.toZero W
                    (@AddZeroClass.toAddZero W
                      (@AddMonoid.toAddZeroClass W
                        (@AddCommMonoid.toAddMonoid W (@AddCommGroup.toAddCommMonoid W inst_1))))))))) := by sorry

alias «UpperTheory».«Reformulated».«B».«SelectionLemmas».«aux11» := P2M_UpperTheory_Reformulated_B_SelectionLemmas_aux11__5b656cfe231c
