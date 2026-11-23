-- Prove2me | Theorems.Thm_P2M_UpperTheory_Reformulated_B_SelectionLemmas_aux12__47cd1097fb73
-- name    : P2M_UpperTheory_Reformulated_B_SelectionLemmas_aux12__47cd1097fb73
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T05:19:42.44813+00:00
-- url     : https://prove2.me/theorems/412afbce-e6f2-46d0-b46a-2b1e6d693513
-- title:
--   P2 M Upper Theory Reformulated B Selection Lemmas aux12  47cd1097fb73: P2 M Upper Theory Reformulated B Selection Lemmas aux12  47cd1097fb73
-- statement:
--   The P2 M Upper Theory Reformulated B Selection Lemmas aux12  47cd1097fb73 construction uses the P2 M Upper Theory Reformulated B Selection Lemmas aux12  47cd1097fb73 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicArithmetic/IntegralCasts/CapelliIdentities/SelectionLemmas.lean#L2139-L2259
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicArithmetic/IntegralCasts/CapelliIdentities/SelectionLemmas.lean#L2139-L2259

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

theorem P2M_UpperTheory_Reformulated_B_SelectionLemmas_aux12__47cd1097fb73.{u_1, u_2} :
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
      (r : R) {x : W},
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
          (@HSMul.hSMul R W W
            (@instHSMul R W
              (@SMulZeroClass.toSMul R W
                (@AddZero.toZero W
                  (@AddZeroClass.toAddZero W
                    (@AddMonoid.toAddZeroClass W (@AddCommMonoid.toAddMonoid W (@AddCommGroup.toAddCommMonoid W inst_1)))))
                (@DistribSMul.toSMulZeroClass R W
                  (@AddMonoid.toAddZeroClass W (@AddCommMonoid.toAddMonoid W (@AddCommGroup.toAddCommMonoid W inst_1)))
                  (@DistribMulAction.toDistribSMul R W
                    (@Semiring.toMonoid R (@CommSemiring.toSemiring R (@CommRing.toCommSemiring R inst)))
                    (@AddCommMonoid.toAddMonoid W (@AddCommGroup.toAddCommMonoid W inst_1))
                    (@Module.toDistribMulAction R W (@CommSemiring.toSemiring R (@CommRing.toCommSemiring R inst))
                      (@AddCommGroup.toAddCommMonoid W inst_1) inst_2)))))
            r x) := by sorry

alias «UpperTheory».«Reformulated».«B».«SelectionLemmas».«aux12» := P2M_UpperTheory_Reformulated_B_SelectionLemmas_aux12__47cd1097fb73
