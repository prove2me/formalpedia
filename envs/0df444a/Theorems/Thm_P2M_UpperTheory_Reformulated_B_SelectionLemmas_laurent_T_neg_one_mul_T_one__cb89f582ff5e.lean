-- Prove2me | Theorems.Thm_P2M_UpperTheory_Reformulated_B_SelectionLemmas_laurent_T_neg_one_mul_T_one__cb89f582ff5e
-- name    : P2M_UpperTheory_Reformulated_B_SelectionLemmas_laurent_T_neg_one_mul_T_one__cb89f582ff5e
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T05:19:20.10193+00:00
-- url     : https://prove2.me/theorems/5aa6ed58-0bb8-4562-9573-fd4199cfd3b3
-- title:
--   P2 M Upper Theory Reformulated B Selection Lemmas laurent T neg one mul T one  cb89f582ff5e: P2 M Upper Theory Reformulated B Selection Lemmas laurent T neg one mul T one  cb89f582ff5e
-- statement:
--   The P2 M Upper Theory Reformulated B Selection Lemmas laurent T neg one mul T one  cb89f582ff5e construction uses the P2 M Upper Theory Reformulated B Selection Lemmas laurent T neg one mul T one  cb89f582ff5e property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicArithmetic/IntegralCasts/CapelliIdentities/SelectionLemmas.lean#L1909-L2075
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicArithmetic/IntegralCasts/CapelliIdentities/SelectionLemmas.lean#L1909-L2075

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

theorem P2M_UpperTheory_Reformulated_B_SelectionLemmas_laurent_T_neg_one_mul_T_one__cb89f582ff5e.{u_1, u_2} :
    ∀ {R : Type u_2} [inst : CommRing R] {W : Type u_1} [inst_1 : AddCommGroup W]
      [inst_2 :
        @_root_.Module R W (@CommSemiring.toSemiring R (@CommRing.toCommSemiring R inst))
          (@AddCommGroup.toAddCommMonoid W inst_1)]
      (S :
        @Submonoid R
          (@MulZeroOneClass.toMulOneClass R
            (@instMulZeroOneClassOfSemiring R (@CommSemiring.toSemiring R (@CommRing.toCommSemiring R inst)))))
      (L :
        @Submodule R W (@CommSemiring.toSemiring R (@CommRing.toCommSemiring R inst))
          (@AddCommGroup.toAddCommMonoid W inst_1) inst_2)
      {x y : W},
      @Membership.mem W (Set W) (@Set.instMembership W)
          (@Set.ofPred W fun (x : W) ↦
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
                              (@SubNegMonoid.toAddMonoid W
                                (@AddGroup.toSubNegMonoid W (@AddCommGroup.toAddGroup W inst_1))))))
                        (@DistribSMul.toSMulZeroClass R W
                          (@AddMonoid.toAddZeroClass W
                            (@SubNegMonoid.toAddMonoid W (@AddGroup.toSubNegMonoid W (@AddCommGroup.toAddGroup W inst_1))))
                          (@DistribMulAction.toDistribSMul R W
                            (@Semiring.toMonoid R (@CommSemiring.toSemiring R (@CommRing.toCommSemiring R inst)))
                            (@SubNegMonoid.toAddMonoid W (@AddGroup.toSubNegMonoid W (@AddCommGroup.toAddGroup W inst_1)))
                            (@Module.toDistribMulAction R W (@CommSemiring.toSemiring R (@CommRing.toCommSemiring R inst))
                              (@AddCommGroup.toAddCommMonoid W inst_1) inst_2)))))
                    s x)))
          x →
        @Membership.mem W (Set W) (@Set.instMembership W)
            (@Set.ofPred W fun (x : W) ↦
              ∃ (s : R),
                And
                  (@Membership.mem R
                    (@Submonoid R
                      (@MulZeroOneClass.toMulOneClass R
                        (@instMulZeroOneClassOfSemiring R (@CommSemiring.toSemiring R (@CommRing.toCommSemiring R inst)))))
                    (@SetLike.instMembership
                      (@Submonoid R
                        (@MulZeroOneClass.toMulOneClass R
                          (@instMulZeroOneClassOfSemiring R
                            (@CommSemiring.toSemiring R (@CommRing.toCommSemiring R inst)))))
                      R
                      (@Submonoid.instSetLike R
                        (@MulZeroOneClass.toMulOneClass R
                          (@instMulZeroOneClassOfSemiring R
                            (@CommSemiring.toSemiring R (@CommRing.toCommSemiring R inst))))))
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
                                (@SubNegMonoid.toAddMonoid W
                                  (@AddGroup.toSubNegMonoid W (@AddCommGroup.toAddGroup W inst_1))))))
                          (@DistribSMul.toSMulZeroClass R W
                            (@AddMonoid.toAddZeroClass W
                              (@SubNegMonoid.toAddMonoid W
                                (@AddGroup.toSubNegMonoid W (@AddCommGroup.toAddGroup W inst_1))))
                            (@DistribMulAction.toDistribSMul R W
                              (@Semiring.toMonoid R (@CommSemiring.toSemiring R (@CommRing.toCommSemiring R inst)))
                              (@SubNegMonoid.toAddMonoid W (@AddGroup.toSubNegMonoid W (@AddCommGroup.toAddGroup W inst_1)))
                              (@Module.toDistribMulAction R W (@CommSemiring.toSemiring R (@CommRing.toCommSemiring R inst))
                                (@AddCommGroup.toAddCommMonoid W inst_1) inst_2)))))
                      s x)))
            y →
          @Membership.mem W (Set W) (@Set.instMembership W)
            (@Set.ofPred W fun (x : W) ↦
              ∃ (s : R),
                And
                  (@Membership.mem R
                    (@Submonoid R
                      (@MulZeroOneClass.toMulOneClass R
                        (@instMulZeroOneClassOfSemiring R (@CommSemiring.toSemiring R (@CommRing.toCommSemiring R inst)))))
                    (@SetLike.instMembership
                      (@Submonoid R
                        (@MulZeroOneClass.toMulOneClass R
                          (@instMulZeroOneClassOfSemiring R
                            (@CommSemiring.toSemiring R (@CommRing.toCommSemiring R inst)))))
                      R
                      (@Submonoid.instSetLike R
                        (@MulZeroOneClass.toMulOneClass R
                          (@instMulZeroOneClassOfSemiring R
                            (@CommSemiring.toSemiring R (@CommRing.toCommSemiring R inst))))))
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
                                (@SubNegMonoid.toAddMonoid W
                                  (@AddGroup.toSubNegMonoid W (@AddCommGroup.toAddGroup W inst_1))))))
                          (@DistribSMul.toSMulZeroClass R W
                            (@AddMonoid.toAddZeroClass W
                              (@SubNegMonoid.toAddMonoid W
                                (@AddGroup.toSubNegMonoid W (@AddCommGroup.toAddGroup W inst_1))))
                            (@DistribMulAction.toDistribSMul R W
                              (@Semiring.toMonoid R (@CommSemiring.toSemiring R (@CommRing.toCommSemiring R inst)))
                              (@SubNegMonoid.toAddMonoid W (@AddGroup.toSubNegMonoid W (@AddCommGroup.toAddGroup W inst_1)))
                              (@Module.toDistribMulAction R W (@CommSemiring.toSemiring R (@CommRing.toCommSemiring R inst))
                                (@AddCommGroup.toAddCommMonoid W inst_1) inst_2)))))
                      s x)))
            (@HAdd.hAdd W W W
              (@instHAdd W
                (@AddZero.toAdd W
                  (@AddZeroClass.toAddZero W
                    (@AddMonoid.toAddZeroClass W (@AddCommMonoid.toAddMonoid W (@AddCommGroup.toAddCommMonoid W inst_1))))))
              x y) := by sorry

alias «UpperTheory».«Reformulated».«B».«SelectionLemmas».«laurent_T_neg_one_mul_T_one» := P2M_UpperTheory_Reformulated_B_SelectionLemmas_laurent_T_neg_one_mul_T_one__cb89f582ff5e
