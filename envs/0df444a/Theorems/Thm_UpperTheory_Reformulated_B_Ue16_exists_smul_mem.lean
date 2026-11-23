-- Prove2me | Theorems.Thm_UpperTheory_Reformulated_B_Ue16_exists_smul_mem
-- name    : UpperTheory.Reformulated.B.Ue16.exists_smul_mem
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T17:41:00.487092+00:00
-- url     : https://prove2.me/theorems/3cf386e2-103e-487e-a306-ff7935b7cd1d
-- title:
--   Ue16: exists smul mem
-- statement:
--   The Ue16 construction uses the exists smul mem property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicArithmetic/IntegralCasts/CapelliIdentities/ImportsExtraTer.lean#L4-L95
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicArithmetic/IntegralCasts/CapelliIdentities/ImportsExtraTer.lean#L4-L95

import Mathlib
import Definitions.Def_Formalism_WeaklyAdmissibleFiltrations_Statement
import Definitions.Def_Development_AutomorphicArithmetic_IntegralCasts_CapelliIdentities_ImportsExtraTer
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false

theorem UpperTheory.Reformulated.B.Ue16.exists_smul_mem :
    ∀ {G : Type} [inst : Group G] {LL : Type} [inst_1 : Field LL] {O : Type} [inst_2 : CommRing O]
      [inst_3 :
        @Algebra O LL (@CommRing.toCommSemiring O inst_2)
          (@DivisionSemiring.toSemiring LL (@Semifield.toDivisionSemiring LL (@Field.toSemifield LL inst_1)))]
      [@IsDomain O (@CommSemiring.toSemiring O (@CommRing.toCommSemiring O inst_2))]
      [@IsFractionRing O (@CommRing.toCommSemiring O inst_2) LL
          (@Semifield.toCommSemiring LL (@Field.toSemifield LL inst_1)) inst_3]
      {V : Type} [inst_6 : AddCommGroup V]
      [inst_7 :
        @_root_.Module LL V
          (@DivisionSemiring.toSemiring LL (@Semifield.toDivisionSemiring LL (@Field.toSemifield LL inst_1)))
          (@AddCommGroup.toAddCommMonoid V inst_6)]
      [inst_8 :
        @_root_.Module O V (@CommSemiring.toSemiring O (@CommRing.toCommSemiring O inst_2))
          (@AddCommGroup.toAddCommMonoid V inst_6)]
      [@IsScalarTower O LL V
          (@Algebra.toSMul O LL (@CommRing.toCommSemiring O inst_2)
            (@DivisionSemiring.toSemiring LL (@Semifield.toDivisionSemiring LL (@Field.toSemifield LL inst_1))) inst_3)
          (@SMulZeroClass.toSMul LL V
            (@AddZero.toZero V
              (@AddZeroClass.toAddZero V
                (@AddMonoid.toAddZeroClass V
                  (@SubNegMonoid.toAddMonoid V (@AddGroup.toSubNegMonoid V (@AddCommGroup.toAddGroup V inst_6))))))
            (@DistribSMul.toSMulZeroClass LL V
              (@AddMonoid.toAddZeroClass V
                (@SubNegMonoid.toAddMonoid V (@AddGroup.toSubNegMonoid V (@AddCommGroup.toAddGroup V inst_6))))
              (@DistribMulAction.toDistribSMul LL V
                (@Semiring.toMonoid LL
                  (@DivisionSemiring.toSemiring LL (@Semifield.toDivisionSemiring LL (@Field.toSemifield LL inst_1))))
                (@SubNegMonoid.toAddMonoid V (@AddGroup.toSubNegMonoid V (@AddCommGroup.toAddGroup V inst_6)))
                (@Module.toDistribMulAction LL V
                  (@DivisionSemiring.toSemiring LL (@Semifield.toDivisionSemiring LL (@Field.toSemifield LL inst_1)))
                  (@AddCommGroup.toAddCommMonoid V inst_6) inst_7))))
          (@SMulZeroClass.toSMul O V
            (@AddZero.toZero V
              (@AddZeroClass.toAddZero V
                (@AddMonoid.toAddZeroClass V
                  (@SubNegMonoid.toAddMonoid V (@AddGroup.toSubNegMonoid V (@AddCommGroup.toAddGroup V inst_6))))))
            (@DistribSMul.toSMulZeroClass O V
              (@AddMonoid.toAddZeroClass V
                (@SubNegMonoid.toAddMonoid V (@AddGroup.toSubNegMonoid V (@AddCommGroup.toAddGroup V inst_6))))
              (@DistribMulAction.toDistribSMul O V
                (@Semiring.toMonoid O (@CommSemiring.toSemiring O (@CommRing.toCommSemiring O inst_2)))
                (@SubNegMonoid.toAddMonoid V (@AddGroup.toSubNegMonoid V (@AddCommGroup.toAddGroup V inst_6)))
                (@Module.toDistribMulAction O V (@CommSemiring.toSemiring O (@CommRing.toCommSemiring O inst_2))
                  (@AddCommGroup.toAddCommMonoid V inst_6) inst_8))))]
      {ρ :
        @Representation LL G V
          (@DivisionSemiring.toSemiring LL (@Semifield.toDivisionSemiring LL (@Field.toSemifield LL inst_1)))
          (@DivInvMonoid.toMonoid G (@Group.toDivInvMonoid G inst)) (@AddCommGroup.toAddCommMonoid V inst_6) inst_7}
      (L : @Formalism.WeaklyAdmissibleFiltrations.Lattice G inst LL inst_1 O inst_2 V inst_6 inst_7 inst_8 ρ) (x : V),
      ∃ (a : O),
        And
          (@Ne O a
            (@OfNat.ofNat O (nat_lit 0)
              (@Zero.toOfNat0 O
                (@MulZeroClass.toZero O
                  (@instMulZeroClassOfSemiring O (@CommSemiring.toSemiring O (@CommRing.toCommSemiring O inst_2)))))))
          (@Membership.mem V
            (@Submodule O V (@CommSemiring.toSemiring O (@CommRing.toCommSemiring O inst_2))
              (@AddCommGroup.toAddCommMonoid V inst_6) inst_8)
            (@SetLike.instMembership
              (@Submodule O V (@CommSemiring.toSemiring O (@CommRing.toCommSemiring O inst_2))
                (@AddCommGroup.toAddCommMonoid V inst_6) inst_8)
              V
              (@Submodule.setLike O V (@CommSemiring.toSemiring O (@CommRing.toCommSemiring O inst_2))
                (@AddCommGroup.toAddCommMonoid V inst_6) inst_8))
            (@Formalism.WeaklyAdmissibleFiltrations.Lattice.T G inst LL inst_1 O inst_2 V inst_6 inst_7 inst_8 ρ L)
            (@HSMul.hSMul O V V
              (@instHSMul O V
                (@SMulZeroClass.toSMul O V
                  (@AddZero.toZero V
                    (@AddZeroClass.toAddZero V
                      (@AddMonoid.toAddZeroClass V
                        (@SubNegMonoid.toAddMonoid V (@AddGroup.toSubNegMonoid V (@AddCommGroup.toAddGroup V inst_6))))))
                  (@DistribSMul.toSMulZeroClass O V
                    (@AddMonoid.toAddZeroClass V
                      (@SubNegMonoid.toAddMonoid V (@AddGroup.toSubNegMonoid V (@AddCommGroup.toAddGroup V inst_6))))
                    (@DistribMulAction.toDistribSMul O V
                      (@Semiring.toMonoid O (@CommSemiring.toSemiring O (@CommRing.toCommSemiring O inst_2)))
                      (@SubNegMonoid.toAddMonoid V (@AddGroup.toSubNegMonoid V (@AddCommGroup.toAddGroup V inst_6)))
                      (@Module.toDistribMulAction O V (@CommSemiring.toSemiring O (@CommRing.toCommSemiring O inst_2))
                        (@AddCommGroup.toAddCommMonoid V inst_6) inst_8)))))
              a x)) := by sorry
