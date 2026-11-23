-- Prove2me | Theorems.Thm_UpperTheory_Reformulated_B_Gub2_fg_Z1T
-- name    : UpperTheory.Reformulated.B.Gub2.fg_Z1T
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-23T18:06:34.124295+00:00
-- url     : https://prove2.me/theorems/c7dd2f21-e100-4a7a-be50-2f6201981b50
-- title:
--   Gub2: fg Z1 T
-- statement:
--   The Gub2 construction uses the fg Z1 T property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicArithmetic/IntegralCasts/CapelliIdentities/FgZ1T.lean#L6-L523
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicArithmetic/IntegralCasts/CapelliIdentities/FgZ1T.lean#L6-L523

import Mathlib
import Definitions.Def_Formalism_WeaklyAdmissibleFiltrations_Statement
import Definitions.Def_Formalism_WeaklyAdmissibleFiltrations_StatementTor
import Definitions.Def_Development_AutomorphicArithmetic_IntegralCasts_CapelliIdentities_CompactQuotientSubmodule
import Definitions.Def_Development_AutomorphicArithmetic_IntegralCasts_CapelliIdentities_FgZ1T
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false

theorem UpperTheory.Reformulated.B.Gub2.fg_Z1T :
    ∀ {G : Type} [inst : Group G] [inst_1 : TopologicalSpace G] {LL O V : Type} [inst_2 : Field LL] [inst_3 : CommRing O]
      [inst_4 :
        @Algebra O LL (@CommRing.toCommSemiring O inst_3)
          (@DivisionSemiring.toSemiring LL (@Semifield.toDivisionSemiring LL (@Field.toSemifield LL inst_2)))]
      [inst_5 : AddCommGroup V]
      [inst_6 :
        @_root_.Module LL V
          (@DivisionSemiring.toSemiring LL (@Semifield.toDivisionSemiring LL (@Field.toSemifield LL inst_2)))
          (@AddCommGroup.toAddCommMonoid V inst_5)]
      [inst_7 :
        @_root_.Module O V (@CommSemiring.toSemiring O (@CommRing.toCommSemiring O inst_3))
          (@AddCommGroup.toAddCommMonoid V inst_5)]
      [inst_8 :
        @IsScalarTower O LL V
          (@Algebra.toSMul O LL (@CommRing.toCommSemiring O inst_3)
            (@DivisionSemiring.toSemiring LL (@Semifield.toDivisionSemiring LL (@Field.toSemifield LL inst_2))) inst_4)
          (@SMulZeroClass.toSMul LL V
            (@AddZero.toZero V
              (@AddZeroClass.toAddZero V
                (@AddMonoid.toAddZeroClass V
                  (@SubNegMonoid.toAddMonoid V (@AddGroup.toSubNegMonoid V (@AddCommGroup.toAddGroup V inst_5))))))
            (@DistribSMul.toSMulZeroClass LL V
              (@AddMonoid.toAddZeroClass V
                (@SubNegMonoid.toAddMonoid V (@AddGroup.toSubNegMonoid V (@AddCommGroup.toAddGroup V inst_5))))
              (@DistribMulAction.toDistribSMul LL V
                (@Semiring.toMonoid LL
                  (@DivisionSemiring.toSemiring LL (@Semifield.toDivisionSemiring LL (@Field.toSemifield LL inst_2))))
                (@SubNegMonoid.toAddMonoid V (@AddGroup.toSubNegMonoid V (@AddCommGroup.toAddGroup V inst_5)))
                (@Module.toDistribMulAction LL V
                  (@DivisionSemiring.toSemiring LL (@Semifield.toDivisionSemiring LL (@Field.toSemifield LL inst_2)))
                  (@AddCommGroup.toAddCommMonoid V inst_5) inst_6))))
          (@SMulZeroClass.toSMul O V
            (@AddZero.toZero V
              (@AddZeroClass.toAddZero V
                (@AddMonoid.toAddZeroClass V
                  (@SubNegMonoid.toAddMonoid V (@AddGroup.toSubNegMonoid V (@AddCommGroup.toAddGroup V inst_5))))))
            (@DistribSMul.toSMulZeroClass O V
              (@AddMonoid.toAddZeroClass V
                (@SubNegMonoid.toAddMonoid V (@AddGroup.toSubNegMonoid V (@AddCommGroup.toAddGroup V inst_5))))
              (@DistribMulAction.toDistribSMul O V
                (@Semiring.toMonoid O (@CommSemiring.toSemiring O (@CommRing.toCommSemiring O inst_3)))
                (@SubNegMonoid.toAddMonoid V (@AddGroup.toSubNegMonoid V (@AddCommGroup.toAddGroup V inst_5)))
                (@Module.toDistribMulAction O V (@CommSemiring.toSemiring O (@CommRing.toCommSemiring O inst_3))
                  (@AddCommGroup.toAddCommMonoid V inst_5) inst_7))))]
      {ρ :
        @Representation LL G V
          (@DivisionSemiring.toSemiring LL (@Semifield.toDivisionSemiring LL (@Field.toSemifield LL inst_2)))
          (@DivInvMonoid.toMonoid G (@Group.toDivInvMonoid G inst)) (@AddCommGroup.toAddCommMonoid V inst_5) inst_6}
      [inst_9 : TopologicalSpace V]
      [inst_10 :
        @ContinuousAdd V inst_9
          (@AddCommMagma.toAdd V
            (@AddCommSemigroup.toAddCommMagma V
              (@AddCommMonoid.toAddCommSemigroup V (@AddCommGroup.toAddCommMonoid V inst_5))))]
      [inst_11 :
        @ContinuousConstSMul LL V inst_9
          (@SMulZeroClass.toSMul LL V
            (@AddZero.toZero V
              (@AddZeroClass.toAddZero V
                (@AddMonoid.toAddZeroClass V
                  (@SubNegMonoid.toAddMonoid V (@AddGroup.toSubNegMonoid V (@AddCommGroup.toAddGroup V inst_5))))))
            (@DistribSMul.toSMulZeroClass LL V
              (@AddMonoid.toAddZeroClass V
                (@SubNegMonoid.toAddMonoid V (@AddGroup.toSubNegMonoid V (@AddCommGroup.toAddGroup V inst_5))))
              (@DistribMulAction.toDistribSMul LL V
                (@Semiring.toMonoid LL
                  (@DivisionSemiring.toSemiring LL (@Semifield.toDivisionSemiring LL (@Field.toSemifield LL inst_2))))
                (@SubNegMonoid.toAddMonoid V (@AddGroup.toSubNegMonoid V (@AddCommGroup.toAddGroup V inst_5)))
                (@Module.toDistribMulAction LL V
                  (@DivisionSemiring.toSemiring LL (@Semifield.toDivisionSemiring LL (@Field.toSemifield LL inst_2)))
                  (@AddCommGroup.toAddCommMonoid V inst_5) inst_6))))]
      [inst_12 : TopologicalSpace LL]
      [@ContinuousSMul LL V
          (@SMulZeroClass.toSMul LL V
            (@AddZero.toZero V
              (@AddZeroClass.toAddZero V
                (@AddMonoid.toAddZeroClass V
                  (@SubNegMonoid.toAddMonoid V (@AddGroup.toSubNegMonoid V (@AddCommGroup.toAddGroup V inst_5))))))
            (@DistribSMul.toSMulZeroClass LL V
              (@AddMonoid.toAddZeroClass V
                (@SubNegMonoid.toAddMonoid V (@AddGroup.toSubNegMonoid V (@AddCommGroup.toAddGroup V inst_5))))
              (@DistribMulAction.toDistribSMul LL V
                (@Semiring.toMonoid LL
                  (@DivisionSemiring.toSemiring LL (@Semifield.toDivisionSemiring LL (@Field.toSemifield LL inst_2))))
                (@SubNegMonoid.toAddMonoid V (@AddGroup.toSubNegMonoid V (@AddCommGroup.toAddGroup V inst_5)))
                (@Module.toDistribMulAction LL V
                  (@DivisionSemiring.toSemiring LL (@Semifield.toDivisionSemiring LL (@Field.toSemifield LL inst_2)))
                  (@AddCommGroup.toAddCommMonoid V inst_5) inst_6))))
          inst_12 inst_9]
      [@IsTopologicalAddGroup V inst_9 (@AddCommGroup.toAddGroup V inst_5)] [@T2Space V inst_9]
      (L : @Formalism.WeaklyAdmissibleFiltrations.Lattice G inst LL inst_2 O inst_3 V inst_5 inst_6 inst_7 ρ) {ϖ : O},
      @Ne LL
          (@DFunLike.coe
            (@RingHom O LL (@Semiring.toNonAssocSemiring O (@CommSemiring.toSemiring O (@CommRing.toCommSemiring O inst_3)))
              (@Semiring.toNonAssocSemiring LL
                (@DivisionSemiring.toSemiring LL (@Semifield.toDivisionSemiring LL (@Field.toSemifield LL inst_2)))))
            O (fun (x : O) ↦ LL)
            (@RingHom.instFunLike O LL
              (@Semiring.toNonAssocSemiring O (@CommSemiring.toSemiring O (@CommRing.toCommSemiring O inst_3)))
              (@Semiring.toNonAssocSemiring LL
                (@DivisionSemiring.toSemiring LL (@Semifield.toDivisionSemiring LL (@Field.toSemifield LL inst_2)))))
            (@Algebra.algebraMap O LL (@CommRing.toCommSemiring O inst_3)
              (@DivisionSemiring.toSemiring LL (@Semifield.toDivisionSemiring LL (@Field.toSemifield LL inst_2))) inst_4)
            ϖ)
          (@OfNat.ofNat LL (nat_lit 0)
            (@Zero.toOfNat0 LL
              (@MulZeroClass.toZero LL
                (@instMulZeroClassOfSemiring LL
                  (@DivisionSemiring.toSemiring LL (@Semifield.toDivisionSemiring LL (@Field.toSemifield LL inst_2))))))) →
        (@Filter.HasBasis V Nat
            (@nhds V inst_9
              (@OfNat.ofNat V (nat_lit 0)
                (@Zero.toOfNat0 V
                  (@NegZeroClass.toZero V
                    (@SubNegZeroMonoid.toNegZeroClass V
                      (@SubtractionMonoid.toSubNegZeroMonoid V
                        (@SubtractionCommMonoid.toSubtractionMonoid V
                          (@AddCommGroup.toDivisionAddCommMonoid V inst_5))))))))
            (fun (x : Nat) ↦ True) fun (n : Nat) ↦
            @Set.image V V
              (fun (x : V) ↦
                @HSMul.hSMul O V V
                  (@instHSMul O V
                    (@SMulZeroClass.toSMul O V
                      (@AddZero.toZero V
                        (@AddZeroClass.toAddZero V
                          (@AddMonoid.toAddZeroClass V
                            (@SubNegMonoid.toAddMonoid V
                              (@AddGroup.toSubNegMonoid V (@AddCommGroup.toAddGroup V inst_5))))))
                      (@DistribSMul.toSMulZeroClass O V
                        (@AddMonoid.toAddZeroClass V
                          (@SubNegMonoid.toAddMonoid V (@AddGroup.toSubNegMonoid V (@AddCommGroup.toAddGroup V inst_5))))
                        (@DistribMulAction.toDistribSMul O V
                          (@Semiring.toMonoid O (@CommSemiring.toSemiring O (@CommRing.toCommSemiring O inst_3)))
                          (@SubNegMonoid.toAddMonoid V (@AddGroup.toSubNegMonoid V (@AddCommGroup.toAddGroup V inst_5)))
                          (@Module.toDistribMulAction O V (@CommSemiring.toSemiring O (@CommRing.toCommSemiring O inst_3))
                            (@AddCommGroup.toAddCommMonoid V inst_5) inst_7)))))
                  (@HPow.hPow O Nat O
                    (@instHPow O Nat
                      (@NPow.toPow O
                        (@Monoid.toNPow O
                          (@Semiring.toMonoid O (@CommSemiring.toSemiring O (@CommRing.toCommSemiring O inst_3))))))
                    ϖ n)
                  x)
              (@SetLike.coe
                (@Submodule O V (@CommSemiring.toSemiring O (@CommRing.toCommSemiring O inst_3))
                  (@AddCommGroup.toAddCommMonoid V inst_5) inst_7)
                V
                (@Submodule.setLike O V (@CommSemiring.toSemiring O (@CommRing.toCommSemiring O inst_3))
                  (@AddCommGroup.toAddCommMonoid V inst_5) inst_7)
                (@Formalism.WeaklyAdmissibleFiltrations.Lattice.T G inst LL inst_2 O inst_3 V inst_5 inst_6 inst_7 ρ L))) →
          @IsCompact LL inst_12
              (@Set.range LL O
                (@DFunLike.coe
                  (@RingHom O LL
                    (@Semiring.toNonAssocSemiring O (@CommSemiring.toSemiring O (@CommRing.toCommSemiring O inst_3)))
                    (@Semiring.toNonAssocSemiring LL
                      (@DivisionSemiring.toSemiring LL (@Semifield.toDivisionSemiring LL (@Field.toSemifield LL inst_2)))))
                  O (fun (x : O) ↦ LL)
                  (@RingHom.instFunLike O LL
                    (@Semiring.toNonAssocSemiring O (@CommSemiring.toSemiring O (@CommRing.toCommSemiring O inst_3)))
                    (@Semiring.toNonAssocSemiring LL
                      (@DivisionSemiring.toSemiring LL (@Semifield.toDivisionSemiring LL (@Field.toSemifield LL inst_2)))))
                  (@Algebra.algebraMap O LL (@CommRing.toCommSemiring O inst_3)
                    (@DivisionSemiring.toSemiring LL (@Semifield.toDivisionSemiring LL (@Field.toSemifield LL inst_2)))
                    inst_4))) →
            ∀
              (hI :
                @Formalism.WeaklyAdmissibleFiltrations.StableSub G inst LL inst_2 O inst_3 inst_4 V inst_5 inst_6 inst_7 inst_8 ρ L
                  (@HSMul.hSMul (@Ideal O (@CommSemiring.toSemiring O (@CommRing.toCommSemiring O inst_3)))
                    (@Submodule O (↥(@Formalism.WeaklyAdmissibleFiltrations.Lattice.T G inst LL inst_2 O inst_3 V inst_5 inst_6 inst_7 ρ L))
                      (@CommSemiring.toSemiring O (@CommRing.toCommSemiring O inst_3))
                      (@Submodule.addCommMonoid O V (@CommSemiring.toSemiring O (@CommRing.toCommSemiring O inst_3))
                        (@AddCommGroup.toAddCommMonoid V inst_5) inst_7
                        (@Formalism.WeaklyAdmissibleFiltrations.Lattice.T G inst LL inst_2 O inst_3 V inst_5 inst_6 inst_7 ρ L))
                      (@Submodule.module O V (@CommSemiring.toSemiring O (@CommRing.toCommSemiring O inst_3))
                        (@AddCommGroup.toAddCommMonoid V inst_5) inst_7
                        (@Formalism.WeaklyAdmissibleFiltrations.Lattice.T G inst LL inst_2 O inst_3 V inst_5 inst_6 inst_7 ρ L)))
                    (@Submodule O (↥(@Formalism.WeaklyAdmissibleFiltrations.Lattice.T G inst LL inst_2 O inst_3 V inst_5 inst_6 inst_7 ρ L))
                      (@CommSemiring.toSemiring O (@CommRing.toCommSemiring O inst_3))
                      (@Submodule.addCommMonoid O V (@CommSemiring.toSemiring O (@CommRing.toCommSemiring O inst_3))
                        (@AddCommGroup.toAddCommMonoid V inst_5) inst_7
                        (@Formalism.WeaklyAdmissibleFiltrations.Lattice.T G inst LL inst_2 O inst_3 V inst_5 inst_6 inst_7 ρ L))
                      (@Submodule.module O V (@CommSemiring.toSemiring O (@CommRing.toCommSemiring O inst_3))
                        (@AddCommGroup.toAddCommMonoid V inst_5) inst_7
                        (@Formalism.WeaklyAdmissibleFiltrations.Lattice.T G inst LL inst_2 O inst_3 V inst_5 inst_6 inst_7 ρ L)))
                    (@instHSMul (@Ideal O (@CommSemiring.toSemiring O (@CommRing.toCommSemiring O inst_3)))
                      (@Submodule O (↥(@Formalism.WeaklyAdmissibleFiltrations.Lattice.T G inst LL inst_2 O inst_3 V inst_5 inst_6 inst_7 ρ L))
                        (@CommSemiring.toSemiring O (@CommRing.toCommSemiring O inst_3))
                        (@Submodule.addCommMonoid O V (@CommSemiring.toSemiring O (@CommRing.toCommSemiring O inst_3))
                          (@AddCommGroup.toAddCommMonoid V inst_5) inst_7
                          (@Formalism.WeaklyAdmissibleFiltrations.Lattice.T G inst LL inst_2 O inst_3 V inst_5 inst_6 inst_7 ρ L))
                        (@Submodule.module O V (@CommSemiring.toSemiring O (@CommRing.toCommSemiring O inst_3))
                          (@AddCommGroup.toAddCommMonoid V inst_5) inst_7
                          (@Formalism.WeaklyAdmissibleFiltrations.Lattice.T G inst LL inst_2 O inst_3 V inst_5 inst_6 inst_7 ρ L)))
                      (@Submodule.instSMul O (@CommSemiring.toSemiring O (@CommRing.toCommSemiring O inst_3)) O
                        (@CommSemiring.toSemiring O (@CommRing.toCommSemiring O inst_3))
                        (@Semiring.toModule O (@CommSemiring.toSemiring O (@CommRing.toCommSemiring O inst_3)))
                        (↥(@Formalism.WeaklyAdmissibleFiltrations.Lattice.T G inst LL inst_2 O inst_3 V inst_5 inst_6 inst_7 ρ L))
                        (@Submodule.addCommMonoid O V (@CommSemiring.toSemiring O (@CommRing.toCommSemiring O inst_3))
                          (@AddCommGroup.toAddCommMonoid V inst_5) inst_7
                          (@Formalism.WeaklyAdmissibleFiltrations.Lattice.T G inst LL inst_2 O inst_3 V inst_5 inst_6 inst_7 ρ L))
                        (@Submodule.module O V (@CommSemiring.toSemiring O (@CommRing.toCommSemiring O inst_3))
                          (@AddCommGroup.toAddCommMonoid V inst_5) inst_7
                          (@Formalism.WeaklyAdmissibleFiltrations.Lattice.T G inst LL inst_2 O inst_3 V inst_5 inst_6 inst_7 ρ L))
                        (@Submodule.module O V (@CommSemiring.toSemiring O (@CommRing.toCommSemiring O inst_3))
                          (@AddCommGroup.toAddCommMonoid V inst_5) inst_7
                          (@Formalism.WeaklyAdmissibleFiltrations.Lattice.T G inst LL inst_2 O inst_3 V inst_5 inst_6 inst_7 ρ L))
                        (@Submodule.isScalarTower' O O V (@CommSemiring.toSemiring O (@CommRing.toCommSemiring O inst_3))
                          (@AddCommGroup.toAddCommMonoid V inst_5) inst_7
                          (@Formalism.WeaklyAdmissibleFiltrations.Lattice.T G inst LL inst_2 O inst_3 V inst_5 inst_6 inst_7 ρ L) O
                          (@instSMulOfMul O
                            (@Distrib.toMul O
                              (@instDistribOfSemiring O (@CommSemiring.toSemiring O (@CommRing.toCommSemiring O inst_3)))))
                          (@SMulZeroClass.toSMul O V
                            (@AddZero.toZero V
                              (@AddZeroClass.toAddZero V
                                (@AddMonoid.toAddZeroClass V
                                  (@AddCommMonoid.toAddMonoid V (@AddCommGroup.toAddCommMonoid V inst_5)))))
                            (@DistribSMul.toSMulZeroClass O V
                              (@AddMonoid.toAddZeroClass V
                                (@AddCommMonoid.toAddMonoid V (@AddCommGroup.toAddCommMonoid V inst_5)))
                              (@DistribMulAction.toDistribSMul O V
                                (@Semiring.toMonoid O (@CommSemiring.toSemiring O (@CommRing.toCommSemiring O inst_3)))
                                (@AddCommMonoid.toAddMonoid V (@AddCommGroup.toAddCommMonoid V inst_5))
                                (@Module.toDistribMulAction O V
                                  (@CommSemiring.toSemiring O (@CommRing.toCommSemiring O inst_3))
                                  (@AddCommGroup.toAddCommMonoid V inst_5) inst_7))))
                          (@instSMulOfMul O
                            (@Distrib.toMul O
                              (@instDistribOfSemiring O (@CommSemiring.toSemiring O (@CommRing.toCommSemiring O inst_3)))))
                          (@SMulZeroClass.toSMul O V
                            (@AddZero.toZero V
                              (@AddZeroClass.toAddZero V
                                (@AddMonoid.toAddZeroClass V
                                  (@AddCommMonoid.toAddMonoid V (@AddCommGroup.toAddCommMonoid V inst_5)))))
                            (@DistribSMul.toSMulZeroClass O V
                              (@AddMonoid.toAddZeroClass V
                                (@AddCommMonoid.toAddMonoid V (@AddCommGroup.toAddCommMonoid V inst_5)))
                              (@DistribMulAction.toDistribSMul O V
                                (@Semiring.toMonoid O (@CommSemiring.toSemiring O (@CommRing.toCommSemiring O inst_3)))
                                (@AddCommMonoid.toAddMonoid V (@AddCommGroup.toAddCommMonoid V inst_5))
                                (@Module.toDistribMulAction O V
                                  (@CommSemiring.toSemiring O (@CommRing.toCommSemiring O inst_3))
                                  (@AddCommGroup.toAddCommMonoid V inst_5) inst_7))))
                          (@SMulZeroClass.toSMul O O
                            (@AddZero.toZero O
                              (@AddZeroClass.toAddZero O
                                (@AddMonoid.toAddZeroClass O
                                  (@AddMonoidWithOne.toAddMonoid O
                                    (@AddCommMonoidWithOne.toAddMonoidWithOne O
                                      (@NonAssocSemiring.toAddCommMonoidWithOne O
                                        (@Semiring.toNonAssocSemiring O
                                          (@CommSemiring.toSemiring O (@CommRing.toCommSemiring O inst_3)))))))))
                            (@DistribSMul.toSMulZeroClass O O
                              (@AddMonoid.toAddZeroClass O
                                (@AddMonoidWithOne.toAddMonoid O
                                  (@AddCommMonoidWithOne.toAddMonoidWithOne O
                                    (@NonAssocSemiring.toAddCommMonoidWithOne O
                                      (@Semiring.toNonAssocSemiring O
                                        (@CommSemiring.toSemiring O (@CommRing.toCommSemiring O inst_3)))))))
                              (@DistribMulAction.toDistribSMul O O
                                (@Semiring.toMonoid O (@CommSemiring.toSemiring O (@CommRing.toCommSemiring O inst_3)))
                                (@AddMonoidWithOne.toAddMonoid O
                                  (@AddCommMonoidWithOne.toAddMonoidWithOne O
                                    (@NonAssocSemiring.toAddCommMonoidWithOne O
                                      (@Semiring.toNonAssocSemiring O
                                        (@CommSemiring.toSemiring O (@CommRing.toCommSemiring O inst_3))))))
                                (@Module.toDistribMulAction O O
                                  (@CommSemiring.toSemiring O (@CommRing.toCommSemiring O inst_3))
                                  (@Semiring.toAddCommMonoid O
                                    (@CommSemiring.toSemiring O (@CommRing.toCommSemiring O inst_3)))
                                  (@Semiring.toModule O
                                    (@CommSemiring.toSemiring O (@CommRing.toCommSemiring O inst_3)))))))
                          (@Submodule.module._proof_1 O V (@CommSemiring.toSemiring O (@CommRing.toCommSemiring O inst_3))
                            (@AddCommGroup.toAddCommMonoid V inst_5) inst_7)
                          (@IsScalarTower.left O V
                            (@Semiring.toMonoid O (@CommSemiring.toSemiring O (@CommRing.toCommSemiring O inst_3)))
                            (@DistribMulAction.toMulAction O V
                              (@Semiring.toMonoid O (@CommSemiring.toSemiring O (@CommRing.toCommSemiring O inst_3)))
                              (@AddCommMonoid.toAddMonoid V (@AddCommGroup.toAddCommMonoid V inst_5))
                              (@Module.toDistribMulAction O V
                                (@CommSemiring.toSemiring O (@CommRing.toCommSemiring O inst_3))
                                (@AddCommGroup.toAddCommMonoid V inst_5) inst_7)))
                          (@Submodule.module._proof_1 O V (@CommSemiring.toSemiring O (@CommRing.toCommSemiring O inst_3))
                            (@AddCommGroup.toAddCommMonoid V inst_5) inst_7))))
                    (@Ideal.span O (@CommSemiring.toSemiring O (@CommRing.toCommSemiring O inst_3))
                      (@Singleton.singleton O (Set O) (@Set.instSingletonSet O)
                        (@HPow.hPow O Nat O
                          (@instHPow O Nat
                            (@NPow.toPow O
                              (@Monoid.toNPow O
                                (@Semiring.toMonoid O (@CommSemiring.toSemiring O (@CommRing.toCommSemiring O inst_3))))))
                          ϖ (@OfNat.ofNat Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))))
                    (@Top.top
                      (@Submodule O (↥(@Formalism.WeaklyAdmissibleFiltrations.Lattice.T G inst LL inst_2 O inst_3 V inst_5 inst_6 inst_7 ρ L))
                        (@CommSemiring.toSemiring O (@CommRing.toCommSemiring O inst_3))
                        (@Submodule.addCommMonoid O V (@CommSemiring.toSemiring O (@CommRing.toCommSemiring O inst_3))
                          (@AddCommGroup.toAddCommMonoid V inst_5) inst_7
                          (@Formalism.WeaklyAdmissibleFiltrations.Lattice.T G inst LL inst_2 O inst_3 V inst_5 inst_6 inst_7 ρ L))
                        (@Submodule.module O V (@CommSemiring.toSemiring O (@CommRing.toCommSemiring O inst_3))
                          (@AddCommGroup.toAddCommMonoid V inst_5) inst_7
                          (@Formalism.WeaklyAdmissibleFiltrations.Lattice.T G inst LL inst_2 O inst_3 V inst_5 inst_6 inst_7 ρ L)))
                      (@Submodule.instTop O (↥(@Formalism.WeaklyAdmissibleFiltrations.Lattice.T G inst LL inst_2 O inst_3 V inst_5 inst_6 inst_7 ρ L))
                        (@CommSemiring.toSemiring O (@CommRing.toCommSemiring O inst_3))
                        (@Submodule.addCommMonoid O V (@CommSemiring.toSemiring O (@CommRing.toCommSemiring O inst_3))
                          (@AddCommGroup.toAddCommMonoid V inst_5) inst_7
                          (@Formalism.WeaklyAdmissibleFiltrations.Lattice.T G inst LL inst_2 O inst_3 V inst_5 inst_6 inst_7 ρ L))
                        (@Submodule.module O V (@CommSemiring.toSemiring O (@CommRing.toCommSemiring O inst_3))
                          (@AddCommGroup.toAddCommMonoid V inst_5) inst_7
                          (@Formalism.WeaklyAdmissibleFiltrations.Lattice.T G inst LL inst_2 O inst_3 V inst_5 inst_6 inst_7 ρ L)))))),
              Finite
                  ↥(@Formalism.WeaklyAdmissibleFiltrations.quotientCocycles G inst LL inst_2 O inst_3 inst_4 V inst_5 inst_6 inst_7 inst_8 ρ inst_1 L
                      (@HSMul.hSMul (@Ideal O (@CommSemiring.toSemiring O (@CommRing.toCommSemiring O inst_3)))
                        (@Submodule O (↥(@Formalism.WeaklyAdmissibleFiltrations.Lattice.T G inst LL inst_2 O inst_3 V inst_5 inst_6 inst_7 ρ L))
                          (@CommSemiring.toSemiring O (@CommRing.toCommSemiring O inst_3))
                          (@Submodule.addCommMonoid O V (@CommSemiring.toSemiring O (@CommRing.toCommSemiring O inst_3))
                            (@AddCommGroup.toAddCommMonoid V inst_5) inst_7
                            (@Formalism.WeaklyAdmissibleFiltrations.Lattice.T G inst LL inst_2 O inst_3 V inst_5 inst_6 inst_7 ρ L))
                          (@Submodule.module O V (@CommSemiring.toSemiring O (@CommRing.toCommSemiring O inst_3))
                            (@AddCommGroup.toAddCommMonoid V inst_5) inst_7
                            (@Formalism.WeaklyAdmissibleFiltrations.Lattice.T G inst LL inst_2 O inst_3 V inst_5 inst_6 inst_7 ρ L)))
                        (@Submodule O (↥(@Formalism.WeaklyAdmissibleFiltrations.Lattice.T G inst LL inst_2 O inst_3 V inst_5 inst_6 inst_7 ρ L))
                          (@CommSemiring.toSemiring O (@CommRing.toCommSemiring O inst_3))
                          (@Submodule.addCommMonoid O V (@CommSemiring.toSemiring O (@CommRing.toCommSemiring O inst_3))
                            (@AddCommGroup.toAddCommMonoid V inst_5) inst_7
                            (@Formalism.WeaklyAdmissibleFiltrations.Lattice.T G inst LL inst_2 O inst_3 V inst_5 inst_6 inst_7 ρ L))
                          (@Submodule.module O V (@CommSemiring.toSemiring O (@CommRing.toCommSemiring O inst_3))
                            (@AddCommGroup.toAddCommMonoid V inst_5) inst_7
                            (@Formalism.WeaklyAdmissibleFiltrations.Lattice.T G inst LL inst_2 O inst_3 V inst_5 inst_6 inst_7 ρ L)))
                        (@instHSMul (@Ideal O (@CommSemiring.toSemiring O (@CommRing.toCommSemiring O inst_3)))
                          (@Submodule O (↥(@Formalism.WeaklyAdmissibleFiltrations.Lattice.T G inst LL inst_2 O inst_3 V inst_5 inst_6 inst_7 ρ L))
                            (@CommSemiring.toSemiring O (@CommRing.toCommSemiring O inst_3))
                            (@Submodule.addCommMonoid O V (@CommSemiring.toSemiring O (@CommRing.toCommSemiring O inst_3))
                              (@AddCommGroup.toAddCommMonoid V inst_5) inst_7
                              (@Formalism.WeaklyAdmissibleFiltrations.Lattice.T G inst LL inst_2 O inst_3 V inst_5 inst_6 inst_7 ρ L))
                            (@Submodule.module O V (@CommSemiring.toSemiring O (@CommRing.toCommSemiring O inst_3))
                              (@AddCommGroup.toAddCommMonoid V inst_5) inst_7
                              (@Formalism.WeaklyAdmissibleFiltrations.Lattice.T G inst LL inst_2 O inst_3 V inst_5 inst_6 inst_7 ρ L)))
                          (@Submodule.instSMul O (@CommSemiring.toSemiring O (@CommRing.toCommSemiring O inst_3)) O
                            (@CommSemiring.toSemiring O (@CommRing.toCommSemiring O inst_3))
                            (@Semiring.toModule O (@CommSemiring.toSemiring O (@CommRing.toCommSemiring O inst_3)))
                            (↥(@Formalism.WeaklyAdmissibleFiltrations.Lattice.T G inst LL inst_2 O inst_3 V inst_5 inst_6 inst_7 ρ L))
                            (@Submodule.addCommMonoid O V (@CommSemiring.toSemiring O (@CommRing.toCommSemiring O inst_3))
                              (@AddCommGroup.toAddCommMonoid V inst_5) inst_7
                              (@Formalism.WeaklyAdmissibleFiltrations.Lattice.T G inst LL inst_2 O inst_3 V inst_5 inst_6 inst_7 ρ L))
                            (@Submodule.module O V (@CommSemiring.toSemiring O (@CommRing.toCommSemiring O inst_3))
                              (@AddCommGroup.toAddCommMonoid V inst_5) inst_7
                              (@Formalism.WeaklyAdmissibleFiltrations.Lattice.T G inst LL inst_2 O inst_3 V inst_5 inst_6 inst_7 ρ L))
                            (@Submodule.module O V (@CommSemiring.toSemiring O (@CommRing.toCommSemiring O inst_3))
                              (@AddCommGroup.toAddCommMonoid V inst_5) inst_7
                              (@Formalism.WeaklyAdmissibleFiltrations.Lattice.T G inst LL inst_2 O inst_3 V inst_5 inst_6 inst_7 ρ L))
                            (@Submodule.isScalarTower' O O V
                              (@CommSemiring.toSemiring O (@CommRing.toCommSemiring O inst_3))
                              (@AddCommGroup.toAddCommMonoid V inst_5) inst_7
                              (@Formalism.WeaklyAdmissibleFiltrations.Lattice.T G inst LL inst_2 O inst_3 V inst_5 inst_6 inst_7 ρ L) O
                              (@instSMulOfMul O
                                (@Distrib.toMul O
                                  (@instDistribOfSemiring O
                                    (@CommSemiring.toSemiring O (@CommRing.toCommSemiring O inst_3)))))
                              (@SMulZeroClass.toSMul O V
                                (@AddZero.toZero V
                                  (@AddZeroClass.toAddZero V
                                    (@AddMonoid.toAddZeroClass V
                                      (@AddCommMonoid.toAddMonoid V (@AddCommGroup.toAddCommMonoid V inst_5)))))
                                (@DistribSMul.toSMulZeroClass O V
                                  (@AddMonoid.toAddZeroClass V
                                    (@AddCommMonoid.toAddMonoid V (@AddCommGroup.toAddCommMonoid V inst_5)))
                                  (@DistribMulAction.toDistribSMul O V
                                    (@Semiring.toMonoid O (@CommSemiring.toSemiring O (@CommRing.toCommSemiring O inst_3)))
                                    (@AddCommMonoid.toAddMonoid V (@AddCommGroup.toAddCommMonoid V inst_5))
                                    (@Module.toDistribMulAction O V
                                      (@CommSemiring.toSemiring O (@CommRing.toCommSemiring O inst_3))
                                      (@AddCommGroup.toAddCommMonoid V inst_5) inst_7))))
                              (@instSMulOfMul O
                                (@Distrib.toMul O
                                  (@instDistribOfSemiring O
                                    (@CommSemiring.toSemiring O (@CommRing.toCommSemiring O inst_3)))))
                              (@SMulZeroClass.toSMul O V
                                (@AddZero.toZero V
                                  (@AddZeroClass.toAddZero V
                                    (@AddMonoid.toAddZeroClass V
                                      (@AddCommMonoid.toAddMonoid V (@AddCommGroup.toAddCommMonoid V inst_5)))))
                                (@DistribSMul.toSMulZeroClass O V
                                  (@AddMonoid.toAddZeroClass V
                                    (@AddCommMonoid.toAddMonoid V (@AddCommGroup.toAddCommMonoid V inst_5)))
                                  (@DistribMulAction.toDistribSMul O V
                                    (@Semiring.toMonoid O (@CommSemiring.toSemiring O (@CommRing.toCommSemiring O inst_3)))
                                    (@AddCommMonoid.toAddMonoid V (@AddCommGroup.toAddCommMonoid V inst_5))
                                    (@Module.toDistribMulAction O V
                                      (@CommSemiring.toSemiring O (@CommRing.toCommSemiring O inst_3))
                                      (@AddCommGroup.toAddCommMonoid V inst_5) inst_7))))
                              (@SMulZeroClass.toSMul O O
                                (@AddZero.toZero O
                                  (@AddZeroClass.toAddZero O
                                    (@AddMonoid.toAddZeroClass O
                                      (@AddMonoidWithOne.toAddMonoid O
                                        (@AddCommMonoidWithOne.toAddMonoidWithOne O
                                          (@NonAssocSemiring.toAddCommMonoidWithOne O
                                            (@Semiring.toNonAssocSemiring O
                                              (@CommSemiring.toSemiring O (@CommRing.toCommSemiring O inst_3)))))))))
                                (@DistribSMul.toSMulZeroClass O O
                                  (@AddMonoid.toAddZeroClass O
                                    (@AddMonoidWithOne.toAddMonoid O
                                      (@AddCommMonoidWithOne.toAddMonoidWithOne O
                                        (@NonAssocSemiring.toAddCommMonoidWithOne O
                                          (@Semiring.toNonAssocSemiring O
                                            (@CommSemiring.toSemiring O (@CommRing.toCommSemiring O inst_3)))))))
                                  (@DistribMulAction.toDistribSMul O O
                                    (@Semiring.toMonoid O (@CommSemiring.toSemiring O (@CommRing.toCommSemiring O inst_3)))
                                    (@AddMonoidWithOne.toAddMonoid O
                                      (@AddCommMonoidWithOne.toAddMonoidWithOne O
                                        (@NonAssocSemiring.toAddCommMonoidWithOne O
                                          (@Semiring.toNonAssocSemiring O
                                            (@CommSemiring.toSemiring O (@CommRing.toCommSemiring O inst_3))))))
                                    (@Module.toDistribMulAction O O
                                      (@CommSemiring.toSemiring O (@CommRing.toCommSemiring O inst_3))
                                      (@Semiring.toAddCommMonoid O
                                        (@CommSemiring.toSemiring O (@CommRing.toCommSemiring O inst_3)))
                                      (@Semiring.toModule O
                                        (@CommSemiring.toSemiring O (@CommRing.toCommSemiring O inst_3)))))))
                              (@Submodule.module._proof_1 O V
                                (@CommSemiring.toSemiring O (@CommRing.toCommSemiring O inst_3))
                                (@AddCommGroup.toAddCommMonoid V inst_5) inst_7)
                              (@IsScalarTower.left O V
                                (@Semiring.toMonoid O (@CommSemiring.toSemiring O (@CommRing.toCommSemiring O inst_3)))
                                (@DistribMulAction.toMulAction O V
                                  (@Semiring.toMonoid O (@CommSemiring.toSemiring O (@CommRing.toCommSemiring O inst_3)))
                                  (@AddCommMonoid.toAddMonoid V (@AddCommGroup.toAddCommMonoid V inst_5))
                                  (@Module.toDistribMulAction O V
                                    (@CommSemiring.toSemiring O (@CommRing.toCommSemiring O inst_3))
                                    (@AddCommGroup.toAddCommMonoid V inst_5) inst_7)))
                              (@Submodule.module._proof_1 O V
                                (@CommSemiring.toSemiring O (@CommRing.toCommSemiring O inst_3))
                                (@AddCommGroup.toAddCommMonoid V inst_5) inst_7))))
                        (@Ideal.span O (@CommSemiring.toSemiring O (@CommRing.toCommSemiring O inst_3))
                          (@Singleton.singleton O (Set O) (@Set.instSingletonSet O)
                            (@HPow.hPow O Nat O
                              (@instHPow O Nat
                                (@NPow.toPow O
                                  (@Monoid.toNPow O
                                    (@Semiring.toMonoid O
                                      (@CommSemiring.toSemiring O (@CommRing.toCommSemiring O inst_3))))))
                              ϖ (@OfNat.ofNat Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))))
                        (@Top.top
                          (@Submodule O (↥(@Formalism.WeaklyAdmissibleFiltrations.Lattice.T G inst LL inst_2 O inst_3 V inst_5 inst_6 inst_7 ρ L))
                            (@CommSemiring.toSemiring O (@CommRing.toCommSemiring O inst_3))
                            (@Submodule.addCommMonoid O V (@CommSemiring.toSemiring O (@CommRing.toCommSemiring O inst_3))
                              (@AddCommGroup.toAddCommMonoid V inst_5) inst_7
                              (@Formalism.WeaklyAdmissibleFiltrations.Lattice.T G inst LL inst_2 O inst_3 V inst_5 inst_6 inst_7 ρ L))
                            (@Submodule.module O V (@CommSemiring.toSemiring O (@CommRing.toCommSemiring O inst_3))
                              (@AddCommGroup.toAddCommMonoid V inst_5) inst_7
                              (@Formalism.WeaklyAdmissibleFiltrations.Lattice.T G inst LL inst_2 O inst_3 V inst_5 inst_6 inst_7 ρ L)))
                          (@Submodule.instTop O (↥(@Formalism.WeaklyAdmissibleFiltrations.Lattice.T G inst LL inst_2 O inst_3 V inst_5 inst_6 inst_7 ρ L))
                            (@CommSemiring.toSemiring O (@CommRing.toCommSemiring O inst_3))
                            (@Submodule.addCommMonoid O V (@CommSemiring.toSemiring O (@CommRing.toCommSemiring O inst_3))
                              (@AddCommGroup.toAddCommMonoid V inst_5) inst_7
                              (@Formalism.WeaklyAdmissibleFiltrations.Lattice.T G inst LL inst_2 O inst_3 V inst_5 inst_6 inst_7 ρ L))
                            (@Submodule.module O V (@CommSemiring.toSemiring O (@CommRing.toCommSemiring O inst_3))
                              (@AddCommGroup.toAddCommMonoid V inst_5) inst_7
                              (@Formalism.WeaklyAdmissibleFiltrations.Lattice.T G inst LL inst_2 O inst_3 V inst_5 inst_6 inst_7 ρ L)))))
                      hI) →
                @Submodule.FG O (G → V) (@CommSemiring.toSemiring O (@CommRing.toCommSemiring O inst_3))
                  (@Pi.addCommMonoid G (fun (a : G) ↦ V) fun (i : G) ↦ @AddCommGroup.toAddCommMonoid V inst_5)
                  (@Pi.Function.module G O V (@CommSemiring.toSemiring O (@CommRing.toCommSemiring O inst_3))
                    (@AddCommGroup.toAddCommMonoid V inst_5) inst_7)
                  (@Formalism.WeaklyAdmissibleFiltrations.latticeCocycles G inst LL inst_2 O inst_3 inst_4 V inst_5 inst_6 inst_7 inst_8 ρ inst_1 inst_9 inst_10
                    inst_11 L) := by sorry
