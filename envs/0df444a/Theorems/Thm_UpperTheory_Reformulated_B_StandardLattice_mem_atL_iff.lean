-- Prove2me | Theorems.Thm_UpperTheory_Reformulated_B_StandardLattice_mem_atL_iff
-- name    : UpperTheory.Reformulated.B.StandardLattice.mem_atL_iff
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T01:41:41.793665+00:00
-- url     : https://prove2.me/theorems/479a5111-a755-408c-a06a-dbd32ebd2b6f
-- title:
--   Standard Lattice: mem at L iff
-- statement:
--   The Standard Lattice construction uses the mem at L iff property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicArithmetic/IntegralCasts/CapelliIdentities/StandardLattice.lean#L337-L520
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicArithmetic/IntegralCasts/CapelliIdentities/StandardLattice.lean#L337-L520

import Mathlib
import Definitions.Def_Development_AutomorphicArithmetic_IntegralCasts_CapelliIdentities_StandardLattice
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
attribute [local instance] UpperTheory.Reformulated.B.StandardLattice.rlAlgebra

theorem UpperTheory.Reformulated.B.StandardLattice.mem_atL_iff :
    ∀ (l : Nat) [hl : Fact (Nat.Prime l)] (K : Type) [inst : Field K] [inst_1 : @NumberField K inst] {V : Type}
      [inst_2 : AddCommGroup V]
      [inst_3 :
        @_root_.Module K V (@DivisionSemiring.toSemiring K (@Semifield.toDivisionSemiring K (@Field.toSemifield K inst)))
          (@AddCommGroup.toAddCommMonoid V inst_2)]
      [inst_4 :
        @_root_.Module (@NumberField.RingOfIntegers K inst) V
          (@CommSemiring.toSemiring (@NumberField.RingOfIntegers K inst)
            (@CommRing.toCommSemiring (@NumberField.RingOfIntegers K inst)
              (@NumberField.instCommRingRingOfIntegers K inst)))
          (@AddCommGroup.toAddCommMonoid V inst_2)]
      [@IsScalarTower (@NumberField.RingOfIntegers K inst) K V
          (@Algebra.toSMul (@NumberField.RingOfIntegers K inst) K
            (@CommRing.toCommSemiring (@NumberField.RingOfIntegers K inst) (@NumberField.instCommRingRingOfIntegers K inst))
            (@DivisionSemiring.toSemiring K (@Semifield.toDivisionSemiring K (@Field.toSemifield K inst)))
            (@NumberField.RingOfIntegers.instAlgebra_1 K inst))
          (@SMulZeroClass.toSMul K V
            (@AddZero.toZero V
              (@AddZeroClass.toAddZero V
                (@AddMonoid.toAddZeroClass V
                  (@SubNegMonoid.toAddMonoid V (@AddGroup.toSubNegMonoid V (@AddCommGroup.toAddGroup V inst_2))))))
            (@DistribSMul.toSMulZeroClass K V
              (@AddMonoid.toAddZeroClass V
                (@SubNegMonoid.toAddMonoid V (@AddGroup.toSubNegMonoid V (@AddCommGroup.toAddGroup V inst_2))))
              (@DistribMulAction.toDistribSMul K V
                (@Semiring.toMonoid K
                  (@DivisionSemiring.toSemiring K (@Semifield.toDivisionSemiring K (@Field.toSemifield K inst))))
                (@SubNegMonoid.toAddMonoid V (@AddGroup.toSubNegMonoid V (@AddCommGroup.toAddGroup V inst_2)))
                (@Module.toDistribMulAction K V
                  (@DivisionSemiring.toSemiring K (@Semifield.toDivisionSemiring K (@Field.toSemifield K inst)))
                  (@AddCommGroup.toAddCommMonoid V inst_2) inst_3))))
          (@SMulZeroClass.toSMul (@NumberField.RingOfIntegers K inst) V
            (@AddZero.toZero V
              (@AddZeroClass.toAddZero V
                (@AddMonoid.toAddZeroClass V
                  (@SubNegMonoid.toAddMonoid V (@AddGroup.toSubNegMonoid V (@AddCommGroup.toAddGroup V inst_2))))))
            (@DistribSMul.toSMulZeroClass (@NumberField.RingOfIntegers K inst) V
              (@AddMonoid.toAddZeroClass V
                (@SubNegMonoid.toAddMonoid V (@AddGroup.toSubNegMonoid V (@AddCommGroup.toAddGroup V inst_2))))
              (@DistribMulAction.toDistribSMul (@NumberField.RingOfIntegers K inst) V
                (@Semiring.toMonoid (@NumberField.RingOfIntegers K inst)
                  (@CommSemiring.toSemiring (@NumberField.RingOfIntegers K inst)
                    (@CommRing.toCommSemiring (@NumberField.RingOfIntegers K inst)
                      (@NumberField.instCommRingRingOfIntegers K inst))))
                (@SubNegMonoid.toAddMonoid V (@AddGroup.toSubNegMonoid V (@AddCommGroup.toAddGroup V inst_2)))
                (@Module.toDistribMulAction (@NumberField.RingOfIntegers K inst) V
                  (@CommSemiring.toSemiring (@NumberField.RingOfIntegers K inst)
                    (@CommRing.toCommSemiring (@NumberField.RingOfIntegers K inst)
                      (@NumberField.instCommRingRingOfIntegers K inst)))
                  (@AddCommGroup.toAddCommMonoid V inst_2) inst_4))))]
      {L :
        @Submodule (@NumberField.RingOfIntegers K inst) V
          (@CommSemiring.toSemiring (@NumberField.RingOfIntegers K inst)
            (@CommRing.toCommSemiring (@NumberField.RingOfIntegers K inst)
              (@NumberField.instCommRingRingOfIntegers K inst)))
          (@AddCommGroup.toAddCommMonoid V inst_2) inst_4}
      {x : V},
      Iff
        (@Membership.mem V
          (@Submodule (@UpperTheory.Reformulated.B.StandardLattice.Rl l hl K inst) V
            (@OreLocalization.instSemiring (@NumberField.RingOfIntegers K inst)
              (@CommSemiring.toSemiring (@NumberField.RingOfIntegers K inst)
                (@CommRing.toCommSemiring (@NumberField.RingOfIntegers K inst)
                  (@NumberField.instCommRingRingOfIntegers K inst)))
              (@UpperTheory.Reformulated.B.StandardLattice.Ml l hl K inst)
              (@OreLocalization.oreSetComm (@NumberField.RingOfIntegers K inst)
                (@CommRing.toCommMonoid (@NumberField.RingOfIntegers K inst)
                  (@NumberField.instCommRingRingOfIntegers K inst))
                (@UpperTheory.Reformulated.B.StandardLattice.Ml l hl K inst)))
            (@AddCommGroup.toAddCommMonoid V inst_2) (@UpperTheory.Reformulated.B.StandardLattice.rlModule l hl K inst inst_1 V inst_2 inst_3))
          (@SetLike.instMembership
            (@Submodule (@UpperTheory.Reformulated.B.StandardLattice.Rl l hl K inst) V
              (@OreLocalization.instSemiring (@NumberField.RingOfIntegers K inst)
                (@CommSemiring.toSemiring (@NumberField.RingOfIntegers K inst)
                  (@CommRing.toCommSemiring (@NumberField.RingOfIntegers K inst)
                    (@NumberField.instCommRingRingOfIntegers K inst)))
                (@UpperTheory.Reformulated.B.StandardLattice.Ml l hl K inst)
                (@OreLocalization.oreSetComm (@NumberField.RingOfIntegers K inst)
                  (@CommRing.toCommMonoid (@NumberField.RingOfIntegers K inst)
                    (@NumberField.instCommRingRingOfIntegers K inst))
                  (@UpperTheory.Reformulated.B.StandardLattice.Ml l hl K inst)))
              (@AddCommGroup.toAddCommMonoid V inst_2) (@UpperTheory.Reformulated.B.StandardLattice.rlModule l hl K inst inst_1 V inst_2 inst_3))
            V
            (@Submodule.setLike (@UpperTheory.Reformulated.B.StandardLattice.Rl l hl K inst) V
              (@OreLocalization.instSemiring (@NumberField.RingOfIntegers K inst)
                (@CommSemiring.toSemiring (@NumberField.RingOfIntegers K inst)
                  (@CommRing.toCommSemiring (@NumberField.RingOfIntegers K inst)
                    (@NumberField.instCommRingRingOfIntegers K inst)))
                (@UpperTheory.Reformulated.B.StandardLattice.Ml l hl K inst)
                (@OreLocalization.oreSetComm (@NumberField.RingOfIntegers K inst)
                  (@CommRing.toCommMonoid (@NumberField.RingOfIntegers K inst)
                    (@NumberField.instCommRingRingOfIntegers K inst))
                  (@UpperTheory.Reformulated.B.StandardLattice.Ml l hl K inst)))
              (@AddCommGroup.toAddCommMonoid V inst_2) (@UpperTheory.Reformulated.B.StandardLattice.rlModule l hl K inst inst_1 V inst_2 inst_3)))
          (@UpperTheory.Reformulated.B.StandardLattice.atL l hl K inst inst_1 V inst_2 inst_3 inst_4 L) x)
        (∃ (s : @NumberField.RingOfIntegers K inst),
          And
            (@Membership.mem (@NumberField.RingOfIntegers K inst)
              (@Submonoid (@NumberField.RingOfIntegers K inst)
                (@MulZeroOneClass.toMulOneClass (@NumberField.RingOfIntegers K inst)
                  (@instMulZeroOneClassOfSemiring (@NumberField.RingOfIntegers K inst)
                    (@CommSemiring.toSemiring (@NumberField.RingOfIntegers K inst)
                      (@CommRing.toCommSemiring (@NumberField.RingOfIntegers K inst)
                        (@NumberField.instCommRingRingOfIntegers K inst))))))
              (@SetLike.instMembership
                (@Submonoid (@NumberField.RingOfIntegers K inst)
                  (@MulZeroOneClass.toMulOneClass (@NumberField.RingOfIntegers K inst)
                    (@instMulZeroOneClassOfSemiring (@NumberField.RingOfIntegers K inst)
                      (@CommSemiring.toSemiring (@NumberField.RingOfIntegers K inst)
                        (@CommRing.toCommSemiring (@NumberField.RingOfIntegers K inst)
                          (@NumberField.instCommRingRingOfIntegers K inst))))))
                (@NumberField.RingOfIntegers K inst)
                (@Submonoid.instSetLike (@NumberField.RingOfIntegers K inst)
                  (@MulZeroOneClass.toMulOneClass (@NumberField.RingOfIntegers K inst)
                    (@instMulZeroOneClassOfSemiring (@NumberField.RingOfIntegers K inst)
                      (@CommSemiring.toSemiring (@NumberField.RingOfIntegers K inst)
                        (@CommRing.toCommSemiring (@NumberField.RingOfIntegers K inst)
                          (@NumberField.instCommRingRingOfIntegers K inst)))))))
              (@UpperTheory.Reformulated.B.StandardLattice.Ml l hl K inst) s)
            (@Membership.mem V
              (@Submodule (@NumberField.RingOfIntegers K inst) V
                (@CommSemiring.toSemiring (@NumberField.RingOfIntegers K inst)
                  (@CommRing.toCommSemiring (@NumberField.RingOfIntegers K inst)
                    (@NumberField.instCommRingRingOfIntegers K inst)))
                (@AddCommGroup.toAddCommMonoid V inst_2) inst_4)
              (@SetLike.instMembership
                (@Submodule (@NumberField.RingOfIntegers K inst) V
                  (@CommSemiring.toSemiring (@NumberField.RingOfIntegers K inst)
                    (@CommRing.toCommSemiring (@NumberField.RingOfIntegers K inst)
                      (@NumberField.instCommRingRingOfIntegers K inst)))
                  (@AddCommGroup.toAddCommMonoid V inst_2) inst_4)
                V
                (@Submodule.setLike (@NumberField.RingOfIntegers K inst) V
                  (@CommSemiring.toSemiring (@NumberField.RingOfIntegers K inst)
                    (@CommRing.toCommSemiring (@NumberField.RingOfIntegers K inst)
                      (@NumberField.instCommRingRingOfIntegers K inst)))
                  (@AddCommGroup.toAddCommMonoid V inst_2) inst_4))
              L
              (@HSMul.hSMul (@NumberField.RingOfIntegers K inst) V V
                (@instHSMul (@NumberField.RingOfIntegers K inst) V
                  (@SMulZeroClass.toSMul (@NumberField.RingOfIntegers K inst) V
                    (@AddZero.toZero V
                      (@AddZeroClass.toAddZero V
                        (@AddMonoid.toAddZeroClass V
                          (@SubNegMonoid.toAddMonoid V (@AddGroup.toSubNegMonoid V (@AddCommGroup.toAddGroup V inst_2))))))
                    (@DistribSMul.toSMulZeroClass (@NumberField.RingOfIntegers K inst) V
                      (@AddMonoid.toAddZeroClass V
                        (@SubNegMonoid.toAddMonoid V (@AddGroup.toSubNegMonoid V (@AddCommGroup.toAddGroup V inst_2))))
                      (@DistribMulAction.toDistribSMul (@NumberField.RingOfIntegers K inst) V
                        (@Semiring.toMonoid (@NumberField.RingOfIntegers K inst)
                          (@CommSemiring.toSemiring (@NumberField.RingOfIntegers K inst)
                            (@CommRing.toCommSemiring (@NumberField.RingOfIntegers K inst)
                              (@NumberField.instCommRingRingOfIntegers K inst))))
                        (@SubNegMonoid.toAddMonoid V (@AddGroup.toSubNegMonoid V (@AddCommGroup.toAddGroup V inst_2)))
                        (@Module.toDistribMulAction (@NumberField.RingOfIntegers K inst) V
                          (@CommSemiring.toSemiring (@NumberField.RingOfIntegers K inst)
                            (@CommRing.toCommSemiring (@NumberField.RingOfIntegers K inst)
                              (@NumberField.instCommRingRingOfIntegers K inst)))
                          (@AddCommGroup.toAddCommMonoid V inst_2) inst_4)))))
                s x))) := by sorry
