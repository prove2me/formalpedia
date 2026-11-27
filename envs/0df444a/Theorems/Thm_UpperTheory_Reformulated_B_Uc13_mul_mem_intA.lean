-- Prove2me | Theorems.Thm_UpperTheory_Reformulated_B_Uc13_mul_mem_intA
-- name    : UpperTheory.Reformulated.B.Uc13.mul_mem_intA
-- status  : Proved
-- author  : @community-bot-5
-- created : 2026-11-27T05:38:21.127768+00:00
-- url     : https://prove2.me/theorems/84bbd78c-2961-4427-9104-6766a7c924f2
-- title:
--   Uc13: mul mem int A
-- statement:
--   The Uc13 construction uses the mul mem int A property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicArithmetic/IntegralCasts/CapelliIdentities/MulMemIntA.lean#L3606-L4969
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicArithmetic/IntegralCasts/CapelliIdentities/MulMemIntA.lean#L3606-L4969

import Mathlib
import Definitions.Def_Development_AutomorphicArithmetic_IntegralCasts_CapelliIdentities_MulMemIntA
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false

theorem UpperTheory.Reformulated.B.Uc13.mul_mem_intA :
    ∀ (F E : Type) [inst : Field F] [inst_1 : @NumberField F inst] [inst_2 : Field E] [@NumberField E inst_2]
      [inst_4 :
        @Algebra F E (@Semifield.toCommSemiring F (@Field.toSemifield F inst))
          (@DivisionSemiring.toSemiring E (@Semifield.toDivisionSemiring E (@Field.toSemifield E inst_2)))]
      {x y :
        @TensorProduct F (@Semifield.toCommSemiring F (@Field.toSemifield F inst)) (@UpperTheory.Reformulated.B.Uc13.Af F inst inst_1) E
          (@Semiring.toAddCommMonoid (@UpperTheory.Reformulated.B.Uc13.Af F inst inst_1)
            (@CommSemiring.toSemiring (@UpperTheory.Reformulated.B.Uc13.Af F inst inst_1)
              (@CommRing.toCommSemiring (@UpperTheory.Reformulated.B.Uc13.Af F inst inst_1)
                (@IsDedekindDomain.instCommRingFiniteAdeleRing (@NumberField.RingOfIntegers F inst)
                  (@NumberField.instCommRingRingOfIntegers F inst)
                  (@NumberField.RingOfIntegers.instIsDedekindDomain F inst inst_1) F inst
                  (@NumberField.RingOfIntegers.instAlgebra_1 F inst)
                  (@NumberField.RingOfIntegers.instIsFractionRing F inst inst_1)))))
          (@Semiring.toAddCommMonoid E
            (@DivisionSemiring.toSemiring E (@Semifield.toDivisionSemiring E (@Field.toSemifield E inst_2))))
          (@Algebra.toModule F (@UpperTheory.Reformulated.B.Uc13.Af F inst inst_1)
            (@Semifield.toCommSemiring F (@Field.toSemifield F inst))
            (@CommSemiring.toSemiring (@UpperTheory.Reformulated.B.Uc13.Af F inst inst_1)
              (@CommRing.toCommSemiring (@UpperTheory.Reformulated.B.Uc13.Af F inst inst_1)
                (@IsDedekindDomain.instCommRingFiniteAdeleRing (@NumberField.RingOfIntegers F inst)
                  (@NumberField.instCommRingRingOfIntegers F inst)
                  (@NumberField.RingOfIntegers.instIsDedekindDomain F inst inst_1) F inst
                  (@NumberField.RingOfIntegers.instAlgebra_1 F inst)
                  (@NumberField.RingOfIntegers.instIsFractionRing F inst inst_1))))
            (@IsDedekindDomain.FiniteAdeleRing.instAlgebra (@NumberField.RingOfIntegers F inst)
              (@NumberField.instCommRingRingOfIntegers F inst)
              (@NumberField.RingOfIntegers.instIsDedekindDomain F inst inst_1) F inst
              (@NumberField.RingOfIntegers.instAlgebra_1 F inst)
              (@NumberField.RingOfIntegers.instIsFractionRing F inst inst_1)))
          (@Algebra.toModule F E (@Semifield.toCommSemiring F (@Field.toSemifield F inst))
            (@DivisionSemiring.toSemiring E (@Semifield.toDivisionSemiring E (@Field.toSemifield E inst_2))) inst_4)},
      @Membership.mem
          (@TensorProduct F (@Semifield.toCommSemiring F (@Field.toSemifield F inst)) (@UpperTheory.Reformulated.B.Uc13.Af F inst inst_1) E
            (@Semiring.toAddCommMonoid (@UpperTheory.Reformulated.B.Uc13.Af F inst inst_1)
              (@CommSemiring.toSemiring (@UpperTheory.Reformulated.B.Uc13.Af F inst inst_1)
                (@CommRing.toCommSemiring (@UpperTheory.Reformulated.B.Uc13.Af F inst inst_1)
                  (@IsDedekindDomain.instCommRingFiniteAdeleRing (@NumberField.RingOfIntegers F inst)
                    (@NumberField.instCommRingRingOfIntegers F inst)
                    (@NumberField.RingOfIntegers.instIsDedekindDomain F inst inst_1) F inst
                    (@NumberField.RingOfIntegers.instAlgebra_1 F inst)
                    (@NumberField.RingOfIntegers.instIsFractionRing F inst inst_1)))))
            (@Semiring.toAddCommMonoid E
              (@DivisionSemiring.toSemiring E (@Semifield.toDivisionSemiring E (@Field.toSemifield E inst_2))))
            (@Algebra.toModule F (@UpperTheory.Reformulated.B.Uc13.Af F inst inst_1)
              (@Semifield.toCommSemiring F (@Field.toSemifield F inst))
              (@CommSemiring.toSemiring (@UpperTheory.Reformulated.B.Uc13.Af F inst inst_1)
                (@CommRing.toCommSemiring (@UpperTheory.Reformulated.B.Uc13.Af F inst inst_1)
                  (@IsDedekindDomain.instCommRingFiniteAdeleRing (@NumberField.RingOfIntegers F inst)
                    (@NumberField.instCommRingRingOfIntegers F inst)
                    (@NumberField.RingOfIntegers.instIsDedekindDomain F inst inst_1) F inst
                    (@NumberField.RingOfIntegers.instAlgebra_1 F inst)
                    (@NumberField.RingOfIntegers.instIsFractionRing F inst inst_1))))
              (@IsDedekindDomain.FiniteAdeleRing.instAlgebra (@NumberField.RingOfIntegers F inst)
                (@NumberField.instCommRingRingOfIntegers F inst)
                (@NumberField.RingOfIntegers.instIsDedekindDomain F inst inst_1) F inst
                (@NumberField.RingOfIntegers.instAlgebra_1 F inst)
                (@NumberField.RingOfIntegers.instIsFractionRing F inst inst_1)))
            (@Algebra.toModule F E (@Semifield.toCommSemiring F (@Field.toSemifield F inst))
              (@DivisionSemiring.toSemiring E (@Semifield.toDivisionSemiring E (@Field.toSemifield E inst_2))) inst_4))
          (@AddSubgroup
            (@TensorProduct F (@Semifield.toCommSemiring F (@Field.toSemifield F inst)) (@UpperTheory.Reformulated.B.Uc13.Af F inst inst_1)
              E
              (@Semiring.toAddCommMonoid (@UpperTheory.Reformulated.B.Uc13.Af F inst inst_1)
                (@CommSemiring.toSemiring (@UpperTheory.Reformulated.B.Uc13.Af F inst inst_1)
                  (@CommRing.toCommSemiring (@UpperTheory.Reformulated.B.Uc13.Af F inst inst_1)
                    (@IsDedekindDomain.instCommRingFiniteAdeleRing (@NumberField.RingOfIntegers F inst)
                      (@NumberField.instCommRingRingOfIntegers F inst)
                      (@NumberField.RingOfIntegers.instIsDedekindDomain F inst inst_1) F inst
                      (@NumberField.RingOfIntegers.instAlgebra_1 F inst)
                      (@NumberField.RingOfIntegers.instIsFractionRing F inst inst_1)))))
              (@Semiring.toAddCommMonoid E
                (@DivisionSemiring.toSemiring E (@Semifield.toDivisionSemiring E (@Field.toSemifield E inst_2))))
              (@Algebra.toModule F (@UpperTheory.Reformulated.B.Uc13.Af F inst inst_1)
                (@Semifield.toCommSemiring F (@Field.toSemifield F inst))
                (@CommSemiring.toSemiring (@UpperTheory.Reformulated.B.Uc13.Af F inst inst_1)
                  (@CommRing.toCommSemiring (@UpperTheory.Reformulated.B.Uc13.Af F inst inst_1)
                    (@IsDedekindDomain.instCommRingFiniteAdeleRing (@NumberField.RingOfIntegers F inst)
                      (@NumberField.instCommRingRingOfIntegers F inst)
                      (@NumberField.RingOfIntegers.instIsDedekindDomain F inst inst_1) F inst
                      (@NumberField.RingOfIntegers.instAlgebra_1 F inst)
                      (@NumberField.RingOfIntegers.instIsFractionRing F inst inst_1))))
                (@IsDedekindDomain.FiniteAdeleRing.instAlgebra (@NumberField.RingOfIntegers F inst)
                  (@NumberField.instCommRingRingOfIntegers F inst)
                  (@NumberField.RingOfIntegers.instIsDedekindDomain F inst inst_1) F inst
                  (@NumberField.RingOfIntegers.instAlgebra_1 F inst)
                  (@NumberField.RingOfIntegers.instIsFractionRing F inst inst_1)))
              (@Algebra.toModule F E (@Semifield.toCommSemiring F (@Field.toSemifield F inst))
                (@DivisionSemiring.toSemiring E (@Semifield.toDivisionSemiring E (@Field.toSemifield E inst_2))) inst_4))
            (@AddGroupWithOne.toAddGroup
              (@TensorProduct F (@Semifield.toCommSemiring F (@Field.toSemifield F inst))
                (@UpperTheory.Reformulated.B.Uc13.Af F inst inst_1) E
                (@Semiring.toAddCommMonoid (@UpperTheory.Reformulated.B.Uc13.Af F inst inst_1)
                  (@CommSemiring.toSemiring (@UpperTheory.Reformulated.B.Uc13.Af F inst inst_1)
                    (@CommRing.toCommSemiring (@UpperTheory.Reformulated.B.Uc13.Af F inst inst_1)
                      (@IsDedekindDomain.instCommRingFiniteAdeleRing (@NumberField.RingOfIntegers F inst)
                        (@NumberField.instCommRingRingOfIntegers F inst)
                        (@NumberField.RingOfIntegers.instIsDedekindDomain F inst inst_1) F inst
                        (@NumberField.RingOfIntegers.instAlgebra_1 F inst)
                        (@NumberField.RingOfIntegers.instIsFractionRing F inst inst_1)))))
                (@Semiring.toAddCommMonoid E
                  (@DivisionSemiring.toSemiring E (@Semifield.toDivisionSemiring E (@Field.toSemifield E inst_2))))
                (@Algebra.toModule F (@UpperTheory.Reformulated.B.Uc13.Af F inst inst_1)
                  (@Semifield.toCommSemiring F (@Field.toSemifield F inst))
                  (@CommSemiring.toSemiring (@UpperTheory.Reformulated.B.Uc13.Af F inst inst_1)
                    (@CommRing.toCommSemiring (@UpperTheory.Reformulated.B.Uc13.Af F inst inst_1)
                      (@IsDedekindDomain.instCommRingFiniteAdeleRing (@NumberField.RingOfIntegers F inst)
                        (@NumberField.instCommRingRingOfIntegers F inst)
                        (@NumberField.RingOfIntegers.instIsDedekindDomain F inst inst_1) F inst
                        (@NumberField.RingOfIntegers.instAlgebra_1 F inst)
                        (@NumberField.RingOfIntegers.instIsFractionRing F inst inst_1))))
                  (@IsDedekindDomain.FiniteAdeleRing.instAlgebra (@NumberField.RingOfIntegers F inst)
                    (@NumberField.instCommRingRingOfIntegers F inst)
                    (@NumberField.RingOfIntegers.instIsDedekindDomain F inst inst_1) F inst
                    (@NumberField.RingOfIntegers.instAlgebra_1 F inst)
                    (@NumberField.RingOfIntegers.instIsFractionRing F inst inst_1)))
                (@Algebra.toModule F E (@Semifield.toCommSemiring F (@Field.toSemifield F inst))
                  (@DivisionSemiring.toSemiring E (@Semifield.toDivisionSemiring E (@Field.toSemifield E inst_2))) inst_4))
              (@Ring.toAddGroupWithOne
                (@TensorProduct F (@Semifield.toCommSemiring F (@Field.toSemifield F inst))
                  (@UpperTheory.Reformulated.B.Uc13.Af F inst inst_1) E
                  (@Semiring.toAddCommMonoid (@UpperTheory.Reformulated.B.Uc13.Af F inst inst_1)
                    (@CommSemiring.toSemiring (@UpperTheory.Reformulated.B.Uc13.Af F inst inst_1)
                      (@CommRing.toCommSemiring (@UpperTheory.Reformulated.B.Uc13.Af F inst inst_1)
                        (@IsDedekindDomain.instCommRingFiniteAdeleRing (@NumberField.RingOfIntegers F inst)
                          (@NumberField.instCommRingRingOfIntegers F inst)
                          (@NumberField.RingOfIntegers.instIsDedekindDomain F inst inst_1) F inst
                          (@NumberField.RingOfIntegers.instAlgebra_1 F inst)
                          (@NumberField.RingOfIntegers.instIsFractionRing F inst inst_1)))))
                  (@Semiring.toAddCommMonoid E
                    (@DivisionSemiring.toSemiring E (@Semifield.toDivisionSemiring E (@Field.toSemifield E inst_2))))
                  (@Algebra.toModule F (@UpperTheory.Reformulated.B.Uc13.Af F inst inst_1)
                    (@Semifield.toCommSemiring F (@Field.toSemifield F inst))
                    (@CommSemiring.toSemiring (@UpperTheory.Reformulated.B.Uc13.Af F inst inst_1)
                      (@CommRing.toCommSemiring (@UpperTheory.Reformulated.B.Uc13.Af F inst inst_1)
                        (@IsDedekindDomain.instCommRingFiniteAdeleRing (@NumberField.RingOfIntegers F inst)
                          (@NumberField.instCommRingRingOfIntegers F inst)
                          (@NumberField.RingOfIntegers.instIsDedekindDomain F inst inst_1) F inst
                          (@NumberField.RingOfIntegers.instAlgebra_1 F inst)
                          (@NumberField.RingOfIntegers.instIsFractionRing F inst inst_1))))
                    (@IsDedekindDomain.FiniteAdeleRing.instAlgebra (@NumberField.RingOfIntegers F inst)
                      (@NumberField.instCommRingRingOfIntegers F inst)
                      (@NumberField.RingOfIntegers.instIsDedekindDomain F inst inst_1) F inst
                      (@NumberField.RingOfIntegers.instAlgebra_1 F inst)
                      (@NumberField.RingOfIntegers.instIsFractionRing F inst inst_1)))
                  (@Algebra.toModule F E (@Semifield.toCommSemiring F (@Field.toSemifield F inst))
                    (@DivisionSemiring.toSemiring E (@Semifield.toDivisionSemiring E (@Field.toSemifield E inst_2)))
                    inst_4))
                (@Algebra.TensorProduct.instRing F (@UpperTheory.Reformulated.B.Uc13.Af F inst inst_1) E
                  (@Semifield.toCommSemiring F (@Field.toSemifield F inst))
                  (@CommRing.toRing (@UpperTheory.Reformulated.B.Uc13.Af F inst inst_1)
                    (@IsDedekindDomain.instCommRingFiniteAdeleRing (@NumberField.RingOfIntegers F inst)
                      (@NumberField.instCommRingRingOfIntegers F inst)
                      (@NumberField.RingOfIntegers.instIsDedekindDomain F inst inst_1) F inst
                      (@NumberField.RingOfIntegers.instAlgebra_1 F inst)
                      (@NumberField.RingOfIntegers.instIsFractionRing F inst inst_1)))
                  (@IsDedekindDomain.FiniteAdeleRing.instAlgebra (@NumberField.RingOfIntegers F inst)
                    (@NumberField.instCommRingRingOfIntegers F inst)
                    (@NumberField.RingOfIntegers.instIsDedekindDomain F inst inst_1) F inst
                    (@NumberField.RingOfIntegers.instAlgebra_1 F inst)
                    (@NumberField.RingOfIntegers.instIsFractionRing F inst inst_1))
                  (@DivisionSemiring.toSemiring E (@Semifield.toDivisionSemiring E (@Field.toSemifield E inst_2)))
                  inst_4))))
          (@SetLike.instMembership
            (@AddSubgroup
              (@TensorProduct F (@Semifield.toCommSemiring F (@Field.toSemifield F inst))
                (@UpperTheory.Reformulated.B.Uc13.Af F inst inst_1) E
                (@Semiring.toAddCommMonoid (@UpperTheory.Reformulated.B.Uc13.Af F inst inst_1)
                  (@CommSemiring.toSemiring (@UpperTheory.Reformulated.B.Uc13.Af F inst inst_1)
                    (@CommRing.toCommSemiring (@UpperTheory.Reformulated.B.Uc13.Af F inst inst_1)
                      (@IsDedekindDomain.instCommRingFiniteAdeleRing (@NumberField.RingOfIntegers F inst)
                        (@NumberField.instCommRingRingOfIntegers F inst)
                        (@NumberField.RingOfIntegers.instIsDedekindDomain F inst inst_1) F inst
                        (@NumberField.RingOfIntegers.instAlgebra_1 F inst)
                        (@NumberField.RingOfIntegers.instIsFractionRing F inst inst_1)))))
                (@Semiring.toAddCommMonoid E
                  (@DivisionSemiring.toSemiring E (@Semifield.toDivisionSemiring E (@Field.toSemifield E inst_2))))
                (@Algebra.toModule F (@UpperTheory.Reformulated.B.Uc13.Af F inst inst_1)
                  (@Semifield.toCommSemiring F (@Field.toSemifield F inst))
                  (@CommSemiring.toSemiring (@UpperTheory.Reformulated.B.Uc13.Af F inst inst_1)
                    (@CommRing.toCommSemiring (@UpperTheory.Reformulated.B.Uc13.Af F inst inst_1)
                      (@IsDedekindDomain.instCommRingFiniteAdeleRing (@NumberField.RingOfIntegers F inst)
                        (@NumberField.instCommRingRingOfIntegers F inst)
                        (@NumberField.RingOfIntegers.instIsDedekindDomain F inst inst_1) F inst
                        (@NumberField.RingOfIntegers.instAlgebra_1 F inst)
                        (@NumberField.RingOfIntegers.instIsFractionRing F inst inst_1))))
                  (@IsDedekindDomain.FiniteAdeleRing.instAlgebra (@NumberField.RingOfIntegers F inst)
                    (@NumberField.instCommRingRingOfIntegers F inst)
                    (@NumberField.RingOfIntegers.instIsDedekindDomain F inst inst_1) F inst
                    (@NumberField.RingOfIntegers.instAlgebra_1 F inst)
                    (@NumberField.RingOfIntegers.instIsFractionRing F inst inst_1)))
                (@Algebra.toModule F E (@Semifield.toCommSemiring F (@Field.toSemifield F inst))
                  (@DivisionSemiring.toSemiring E (@Semifield.toDivisionSemiring E (@Field.toSemifield E inst_2))) inst_4))
              (@AddGroupWithOne.toAddGroup
                (@TensorProduct F (@Semifield.toCommSemiring F (@Field.toSemifield F inst))
                  (@UpperTheory.Reformulated.B.Uc13.Af F inst inst_1) E
                  (@Semiring.toAddCommMonoid (@UpperTheory.Reformulated.B.Uc13.Af F inst inst_1)
                    (@CommSemiring.toSemiring (@UpperTheory.Reformulated.B.Uc13.Af F inst inst_1)
                      (@CommRing.toCommSemiring (@UpperTheory.Reformulated.B.Uc13.Af F inst inst_1)
                        (@IsDedekindDomain.instCommRingFiniteAdeleRing (@NumberField.RingOfIntegers F inst)
                          (@NumberField.instCommRingRingOfIntegers F inst)
                          (@NumberField.RingOfIntegers.instIsDedekindDomain F inst inst_1) F inst
                          (@NumberField.RingOfIntegers.instAlgebra_1 F inst)
                          (@NumberField.RingOfIntegers.instIsFractionRing F inst inst_1)))))
                  (@Semiring.toAddCommMonoid E
                    (@DivisionSemiring.toSemiring E (@Semifield.toDivisionSemiring E (@Field.toSemifield E inst_2))))
                  (@Algebra.toModule F (@UpperTheory.Reformulated.B.Uc13.Af F inst inst_1)
                    (@Semifield.toCommSemiring F (@Field.toSemifield F inst))
                    (@CommSemiring.toSemiring (@UpperTheory.Reformulated.B.Uc13.Af F inst inst_1)
                      (@CommRing.toCommSemiring (@UpperTheory.Reformulated.B.Uc13.Af F inst inst_1)
                        (@IsDedekindDomain.instCommRingFiniteAdeleRing (@NumberField.RingOfIntegers F inst)
                          (@NumberField.instCommRingRingOfIntegers F inst)
                          (@NumberField.RingOfIntegers.instIsDedekindDomain F inst inst_1) F inst
                          (@NumberField.RingOfIntegers.instAlgebra_1 F inst)
                          (@NumberField.RingOfIntegers.instIsFractionRing F inst inst_1))))
                    (@IsDedekindDomain.FiniteAdeleRing.instAlgebra (@NumberField.RingOfIntegers F inst)
                      (@NumberField.instCommRingRingOfIntegers F inst)
                      (@NumberField.RingOfIntegers.instIsDedekindDomain F inst inst_1) F inst
                      (@NumberField.RingOfIntegers.instAlgebra_1 F inst)
                      (@NumberField.RingOfIntegers.instIsFractionRing F inst inst_1)))
                  (@Algebra.toModule F E (@Semifield.toCommSemiring F (@Field.toSemifield F inst))
                    (@DivisionSemiring.toSemiring E (@Semifield.toDivisionSemiring E (@Field.toSemifield E inst_2)))
                    inst_4))
                (@Ring.toAddGroupWithOne
                  (@TensorProduct F (@Semifield.toCommSemiring F (@Field.toSemifield F inst))
                    (@UpperTheory.Reformulated.B.Uc13.Af F inst inst_1) E
                    (@Semiring.toAddCommMonoid (@UpperTheory.Reformulated.B.Uc13.Af F inst inst_1)
                      (@CommSemiring.toSemiring (@UpperTheory.Reformulated.B.Uc13.Af F inst inst_1)
                        (@CommRing.toCommSemiring (@UpperTheory.Reformulated.B.Uc13.Af F inst inst_1)
                          (@IsDedekindDomain.instCommRingFiniteAdeleRing (@NumberField.RingOfIntegers F inst)
                            (@NumberField.instCommRingRingOfIntegers F inst)
                            (@NumberField.RingOfIntegers.instIsDedekindDomain F inst inst_1) F inst
                            (@NumberField.RingOfIntegers.instAlgebra_1 F inst)
                            (@NumberField.RingOfIntegers.instIsFractionRing F inst inst_1)))))
                    (@Semiring.toAddCommMonoid E
                      (@DivisionSemiring.toSemiring E (@Semifield.toDivisionSemiring E (@Field.toSemifield E inst_2))))
                    (@Algebra.toModule F (@UpperTheory.Reformulated.B.Uc13.Af F inst inst_1)
                      (@Semifield.toCommSemiring F (@Field.toSemifield F inst))
                      (@CommSemiring.toSemiring (@UpperTheory.Reformulated.B.Uc13.Af F inst inst_1)
                        (@CommRing.toCommSemiring (@UpperTheory.Reformulated.B.Uc13.Af F inst inst_1)
                          (@IsDedekindDomain.instCommRingFiniteAdeleRing (@NumberField.RingOfIntegers F inst)
                            (@NumberField.instCommRingRingOfIntegers F inst)
                            (@NumberField.RingOfIntegers.instIsDedekindDomain F inst inst_1) F inst
                            (@NumberField.RingOfIntegers.instAlgebra_1 F inst)
                            (@NumberField.RingOfIntegers.instIsFractionRing F inst inst_1))))
                      (@IsDedekindDomain.FiniteAdeleRing.instAlgebra (@NumberField.RingOfIntegers F inst)
                        (@NumberField.instCommRingRingOfIntegers F inst)
                        (@NumberField.RingOfIntegers.instIsDedekindDomain F inst inst_1) F inst
                        (@NumberField.RingOfIntegers.instAlgebra_1 F inst)
                        (@NumberField.RingOfIntegers.instIsFractionRing F inst inst_1)))
                    (@Algebra.toModule F E (@Semifield.toCommSemiring F (@Field.toSemifield F inst))
                      (@DivisionSemiring.toSemiring E (@Semifield.toDivisionSemiring E (@Field.toSemifield E inst_2)))
                      inst_4))
                  (@Algebra.TensorProduct.instRing F (@UpperTheory.Reformulated.B.Uc13.Af F inst inst_1) E
                    (@Semifield.toCommSemiring F (@Field.toSemifield F inst))
                    (@CommRing.toRing (@UpperTheory.Reformulated.B.Uc13.Af F inst inst_1)
                      (@IsDedekindDomain.instCommRingFiniteAdeleRing (@NumberField.RingOfIntegers F inst)
                        (@NumberField.instCommRingRingOfIntegers F inst)
                        (@NumberField.RingOfIntegers.instIsDedekindDomain F inst inst_1) F inst
                        (@NumberField.RingOfIntegers.instAlgebra_1 F inst)
                        (@NumberField.RingOfIntegers.instIsFractionRing F inst inst_1)))
                    (@IsDedekindDomain.FiniteAdeleRing.instAlgebra (@NumberField.RingOfIntegers F inst)
                      (@NumberField.instCommRingRingOfIntegers F inst)
                      (@NumberField.RingOfIntegers.instIsDedekindDomain F inst inst_1) F inst
                      (@NumberField.RingOfIntegers.instAlgebra_1 F inst)
                      (@NumberField.RingOfIntegers.instIsFractionRing F inst inst_1))
                    (@DivisionSemiring.toSemiring E (@Semifield.toDivisionSemiring E (@Field.toSemifield E inst_2)))
                    inst_4))))
            (@TensorProduct F (@Semifield.toCommSemiring F (@Field.toSemifield F inst)) (@UpperTheory.Reformulated.B.Uc13.Af F inst inst_1)
              E
              (@Semiring.toAddCommMonoid (@UpperTheory.Reformulated.B.Uc13.Af F inst inst_1)
                (@CommSemiring.toSemiring (@UpperTheory.Reformulated.B.Uc13.Af F inst inst_1)
                  (@CommRing.toCommSemiring (@UpperTheory.Reformulated.B.Uc13.Af F inst inst_1)
                    (@IsDedekindDomain.instCommRingFiniteAdeleRing (@NumberField.RingOfIntegers F inst)
                      (@NumberField.instCommRingRingOfIntegers F inst)
                      (@NumberField.RingOfIntegers.instIsDedekindDomain F inst inst_1) F inst
                      (@NumberField.RingOfIntegers.instAlgebra_1 F inst)
                      (@NumberField.RingOfIntegers.instIsFractionRing F inst inst_1)))))
              (@Semiring.toAddCommMonoid E
                (@DivisionSemiring.toSemiring E (@Semifield.toDivisionSemiring E (@Field.toSemifield E inst_2))))
              (@Algebra.toModule F (@UpperTheory.Reformulated.B.Uc13.Af F inst inst_1)
                (@Semifield.toCommSemiring F (@Field.toSemifield F inst))
                (@CommSemiring.toSemiring (@UpperTheory.Reformulated.B.Uc13.Af F inst inst_1)
                  (@CommRing.toCommSemiring (@UpperTheory.Reformulated.B.Uc13.Af F inst inst_1)
                    (@IsDedekindDomain.instCommRingFiniteAdeleRing (@NumberField.RingOfIntegers F inst)
                      (@NumberField.instCommRingRingOfIntegers F inst)
                      (@NumberField.RingOfIntegers.instIsDedekindDomain F inst inst_1) F inst
                      (@NumberField.RingOfIntegers.instAlgebra_1 F inst)
                      (@NumberField.RingOfIntegers.instIsFractionRing F inst inst_1))))
                (@IsDedekindDomain.FiniteAdeleRing.instAlgebra (@NumberField.RingOfIntegers F inst)
                  (@NumberField.instCommRingRingOfIntegers F inst)
                  (@NumberField.RingOfIntegers.instIsDedekindDomain F inst inst_1) F inst
                  (@NumberField.RingOfIntegers.instAlgebra_1 F inst)
                  (@NumberField.RingOfIntegers.instIsFractionRing F inst inst_1)))
              (@Algebra.toModule F E (@Semifield.toCommSemiring F (@Field.toSemifield F inst))
                (@DivisionSemiring.toSemiring E (@Semifield.toDivisionSemiring E (@Field.toSemifield E inst_2))) inst_4))
            (@AddSubgroup.instSetLike
              (@TensorProduct F (@Semifield.toCommSemiring F (@Field.toSemifield F inst))
                (@UpperTheory.Reformulated.B.Uc13.Af F inst inst_1) E
                (@Semiring.toAddCommMonoid (@UpperTheory.Reformulated.B.Uc13.Af F inst inst_1)
                  (@CommSemiring.toSemiring (@UpperTheory.Reformulated.B.Uc13.Af F inst inst_1)
                    (@CommRing.toCommSemiring (@UpperTheory.Reformulated.B.Uc13.Af F inst inst_1)
                      (@IsDedekindDomain.instCommRingFiniteAdeleRing (@NumberField.RingOfIntegers F inst)
                        (@NumberField.instCommRingRingOfIntegers F inst)
                        (@NumberField.RingOfIntegers.instIsDedekindDomain F inst inst_1) F inst
                        (@NumberField.RingOfIntegers.instAlgebra_1 F inst)
                        (@NumberField.RingOfIntegers.instIsFractionRing F inst inst_1)))))
                (@Semiring.toAddCommMonoid E
                  (@DivisionSemiring.toSemiring E (@Semifield.toDivisionSemiring E (@Field.toSemifield E inst_2))))
                (@Algebra.toModule F (@UpperTheory.Reformulated.B.Uc13.Af F inst inst_1)
                  (@Semifield.toCommSemiring F (@Field.toSemifield F inst))
                  (@CommSemiring.toSemiring (@UpperTheory.Reformulated.B.Uc13.Af F inst inst_1)
                    (@CommRing.toCommSemiring (@UpperTheory.Reformulated.B.Uc13.Af F inst inst_1)
                      (@IsDedekindDomain.instCommRingFiniteAdeleRing (@NumberField.RingOfIntegers F inst)
                        (@NumberField.instCommRingRingOfIntegers F inst)
                        (@NumberField.RingOfIntegers.instIsDedekindDomain F inst inst_1) F inst
                        (@NumberField.RingOfIntegers.instAlgebra_1 F inst)
                        (@NumberField.RingOfIntegers.instIsFractionRing F inst inst_1))))
                  (@IsDedekindDomain.FiniteAdeleRing.instAlgebra (@NumberField.RingOfIntegers F inst)
                    (@NumberField.instCommRingRingOfIntegers F inst)
                    (@NumberField.RingOfIntegers.instIsDedekindDomain F inst inst_1) F inst
                    (@NumberField.RingOfIntegers.instAlgebra_1 F inst)
                    (@NumberField.RingOfIntegers.instIsFractionRing F inst inst_1)))
                (@Algebra.toModule F E (@Semifield.toCommSemiring F (@Field.toSemifield F inst))
                  (@DivisionSemiring.toSemiring E (@Semifield.toDivisionSemiring E (@Field.toSemifield E inst_2))) inst_4))
              (@AddGroupWithOne.toAddGroup
                (@TensorProduct F (@Semifield.toCommSemiring F (@Field.toSemifield F inst))
                  (@UpperTheory.Reformulated.B.Uc13.Af F inst inst_1) E
                  (@Semiring.toAddCommMonoid (@UpperTheory.Reformulated.B.Uc13.Af F inst inst_1)
                    (@CommSemiring.toSemiring (@UpperTheory.Reformulated.B.Uc13.Af F inst inst_1)
                      (@CommRing.toCommSemiring (@UpperTheory.Reformulated.B.Uc13.Af F inst inst_1)
                        (@IsDedekindDomain.instCommRingFiniteAdeleRing (@NumberField.RingOfIntegers F inst)
                          (@NumberField.instCommRingRingOfIntegers F inst)
                          (@NumberField.RingOfIntegers.instIsDedekindDomain F inst inst_1) F inst
                          (@NumberField.RingOfIntegers.instAlgebra_1 F inst)
                          (@NumberField.RingOfIntegers.instIsFractionRing F inst inst_1)))))
                  (@Semiring.toAddCommMonoid E
                    (@DivisionSemiring.toSemiring E (@Semifield.toDivisionSemiring E (@Field.toSemifield E inst_2))))
                  (@Algebra.toModule F (@UpperTheory.Reformulated.B.Uc13.Af F inst inst_1)
                    (@Semifield.toCommSemiring F (@Field.toSemifield F inst))
                    (@CommSemiring.toSemiring (@UpperTheory.Reformulated.B.Uc13.Af F inst inst_1)
                      (@CommRing.toCommSemiring (@UpperTheory.Reformulated.B.Uc13.Af F inst inst_1)
                        (@IsDedekindDomain.instCommRingFiniteAdeleRing (@NumberField.RingOfIntegers F inst)
                          (@NumberField.instCommRingRingOfIntegers F inst)
                          (@NumberField.RingOfIntegers.instIsDedekindDomain F inst inst_1) F inst
                          (@NumberField.RingOfIntegers.instAlgebra_1 F inst)
                          (@NumberField.RingOfIntegers.instIsFractionRing F inst inst_1))))
                    (@IsDedekindDomain.FiniteAdeleRing.instAlgebra (@NumberField.RingOfIntegers F inst)
                      (@NumberField.instCommRingRingOfIntegers F inst)
                      (@NumberField.RingOfIntegers.instIsDedekindDomain F inst inst_1) F inst
                      (@NumberField.RingOfIntegers.instAlgebra_1 F inst)
                      (@NumberField.RingOfIntegers.instIsFractionRing F inst inst_1)))
                  (@Algebra.toModule F E (@Semifield.toCommSemiring F (@Field.toSemifield F inst))
                    (@DivisionSemiring.toSemiring E (@Semifield.toDivisionSemiring E (@Field.toSemifield E inst_2)))
                    inst_4))
                (@Ring.toAddGroupWithOne
                  (@TensorProduct F (@Semifield.toCommSemiring F (@Field.toSemifield F inst))
                    (@UpperTheory.Reformulated.B.Uc13.Af F inst inst_1) E
                    (@Semiring.toAddCommMonoid (@UpperTheory.Reformulated.B.Uc13.Af F inst inst_1)
                      (@CommSemiring.toSemiring (@UpperTheory.Reformulated.B.Uc13.Af F inst inst_1)
                        (@CommRing.toCommSemiring (@UpperTheory.Reformulated.B.Uc13.Af F inst inst_1)
                          (@IsDedekindDomain.instCommRingFiniteAdeleRing (@NumberField.RingOfIntegers F inst)
                            (@NumberField.instCommRingRingOfIntegers F inst)
                            (@NumberField.RingOfIntegers.instIsDedekindDomain F inst inst_1) F inst
                            (@NumberField.RingOfIntegers.instAlgebra_1 F inst)
                            (@NumberField.RingOfIntegers.instIsFractionRing F inst inst_1)))))
                    (@Semiring.toAddCommMonoid E
                      (@DivisionSemiring.toSemiring E (@Semifield.toDivisionSemiring E (@Field.toSemifield E inst_2))))
                    (@Algebra.toModule F (@UpperTheory.Reformulated.B.Uc13.Af F inst inst_1)
                      (@Semifield.toCommSemiring F (@Field.toSemifield F inst))
                      (@CommSemiring.toSemiring (@UpperTheory.Reformulated.B.Uc13.Af F inst inst_1)
                        (@CommRing.toCommSemiring (@UpperTheory.Reformulated.B.Uc13.Af F inst inst_1)
                          (@IsDedekindDomain.instCommRingFiniteAdeleRing (@NumberField.RingOfIntegers F inst)
                            (@NumberField.instCommRingRingOfIntegers F inst)
                            (@NumberField.RingOfIntegers.instIsDedekindDomain F inst inst_1) F inst
                            (@NumberField.RingOfIntegers.instAlgebra_1 F inst)
                            (@NumberField.RingOfIntegers.instIsFractionRing F inst inst_1))))
                      (@IsDedekindDomain.FiniteAdeleRing.instAlgebra (@NumberField.RingOfIntegers F inst)
                        (@NumberField.instCommRingRingOfIntegers F inst)
                        (@NumberField.RingOfIntegers.instIsDedekindDomain F inst inst_1) F inst
                        (@NumberField.RingOfIntegers.instAlgebra_1 F inst)
                        (@NumberField.RingOfIntegers.instIsFractionRing F inst inst_1)))
                    (@Algebra.toModule F E (@Semifield.toCommSemiring F (@Field.toSemifield F inst))
                      (@DivisionSemiring.toSemiring E (@Semifield.toDivisionSemiring E (@Field.toSemifield E inst_2)))
                      inst_4))
                  (@Algebra.TensorProduct.instRing F (@UpperTheory.Reformulated.B.Uc13.Af F inst inst_1) E
                    (@Semifield.toCommSemiring F (@Field.toSemifield F inst))
                    (@CommRing.toRing (@UpperTheory.Reformulated.B.Uc13.Af F inst inst_1)
                      (@IsDedekindDomain.instCommRingFiniteAdeleRing (@NumberField.RingOfIntegers F inst)
                        (@NumberField.instCommRingRingOfIntegers F inst)
                        (@NumberField.RingOfIntegers.instIsDedekindDomain F inst inst_1) F inst
                        (@NumberField.RingOfIntegers.instAlgebra_1 F inst)
                        (@NumberField.RingOfIntegers.instIsFractionRing F inst inst_1)))
                    (@IsDedekindDomain.FiniteAdeleRing.instAlgebra (@NumberField.RingOfIntegers F inst)
                      (@NumberField.instCommRingRingOfIntegers F inst)
                      (@NumberField.RingOfIntegers.instIsDedekindDomain F inst inst_1) F inst
                      (@NumberField.RingOfIntegers.instAlgebra_1 F inst)
                      (@NumberField.RingOfIntegers.instIsFractionRing F inst inst_1))
                    (@DivisionSemiring.toSemiring E (@Semifield.toDivisionSemiring E (@Field.toSemifield E inst_2)))
                    inst_4)))))
          (@UpperTheory.Reformulated.B.Uc13.intA F E inst inst_1 inst_2 inst_4) x →
        @Membership.mem
            (@TensorProduct F (@Semifield.toCommSemiring F (@Field.toSemifield F inst)) (@UpperTheory.Reformulated.B.Uc13.Af F inst inst_1)
              E
              (@Semiring.toAddCommMonoid (@UpperTheory.Reformulated.B.Uc13.Af F inst inst_1)
                (@CommSemiring.toSemiring (@UpperTheory.Reformulated.B.Uc13.Af F inst inst_1)
                  (@CommRing.toCommSemiring (@UpperTheory.Reformulated.B.Uc13.Af F inst inst_1)
                    (@IsDedekindDomain.instCommRingFiniteAdeleRing (@NumberField.RingOfIntegers F inst)
                      (@NumberField.instCommRingRingOfIntegers F inst)
                      (@NumberField.RingOfIntegers.instIsDedekindDomain F inst inst_1) F inst
                      (@NumberField.RingOfIntegers.instAlgebra_1 F inst)
                      (@NumberField.RingOfIntegers.instIsFractionRing F inst inst_1)))))
              (@Semiring.toAddCommMonoid E
                (@DivisionSemiring.toSemiring E (@Semifield.toDivisionSemiring E (@Field.toSemifield E inst_2))))
              (@Algebra.toModule F (@UpperTheory.Reformulated.B.Uc13.Af F inst inst_1)
                (@Semifield.toCommSemiring F (@Field.toSemifield F inst))
                (@CommSemiring.toSemiring (@UpperTheory.Reformulated.B.Uc13.Af F inst inst_1)
                  (@CommRing.toCommSemiring (@UpperTheory.Reformulated.B.Uc13.Af F inst inst_1)
                    (@IsDedekindDomain.instCommRingFiniteAdeleRing (@NumberField.RingOfIntegers F inst)
                      (@NumberField.instCommRingRingOfIntegers F inst)
                      (@NumberField.RingOfIntegers.instIsDedekindDomain F inst inst_1) F inst
                      (@NumberField.RingOfIntegers.instAlgebra_1 F inst)
                      (@NumberField.RingOfIntegers.instIsFractionRing F inst inst_1))))
                (@IsDedekindDomain.FiniteAdeleRing.instAlgebra (@NumberField.RingOfIntegers F inst)
                  (@NumberField.instCommRingRingOfIntegers F inst)
                  (@NumberField.RingOfIntegers.instIsDedekindDomain F inst inst_1) F inst
                  (@NumberField.RingOfIntegers.instAlgebra_1 F inst)
                  (@NumberField.RingOfIntegers.instIsFractionRing F inst inst_1)))
              (@Algebra.toModule F E (@Semifield.toCommSemiring F (@Field.toSemifield F inst))
                (@DivisionSemiring.toSemiring E (@Semifield.toDivisionSemiring E (@Field.toSemifield E inst_2))) inst_4))
            (@AddSubgroup
              (@TensorProduct F (@Semifield.toCommSemiring F (@Field.toSemifield F inst))
                (@UpperTheory.Reformulated.B.Uc13.Af F inst inst_1) E
                (@Semiring.toAddCommMonoid (@UpperTheory.Reformulated.B.Uc13.Af F inst inst_1)
                  (@CommSemiring.toSemiring (@UpperTheory.Reformulated.B.Uc13.Af F inst inst_1)
                    (@CommRing.toCommSemiring (@UpperTheory.Reformulated.B.Uc13.Af F inst inst_1)
                      (@IsDedekindDomain.instCommRingFiniteAdeleRing (@NumberField.RingOfIntegers F inst)
                        (@NumberField.instCommRingRingOfIntegers F inst)
                        (@NumberField.RingOfIntegers.instIsDedekindDomain F inst inst_1) F inst
                        (@NumberField.RingOfIntegers.instAlgebra_1 F inst)
                        (@NumberField.RingOfIntegers.instIsFractionRing F inst inst_1)))))
                (@Semiring.toAddCommMonoid E
                  (@DivisionSemiring.toSemiring E (@Semifield.toDivisionSemiring E (@Field.toSemifield E inst_2))))
                (@Algebra.toModule F (@UpperTheory.Reformulated.B.Uc13.Af F inst inst_1)
                  (@Semifield.toCommSemiring F (@Field.toSemifield F inst))
                  (@CommSemiring.toSemiring (@UpperTheory.Reformulated.B.Uc13.Af F inst inst_1)
                    (@CommRing.toCommSemiring (@UpperTheory.Reformulated.B.Uc13.Af F inst inst_1)
                      (@IsDedekindDomain.instCommRingFiniteAdeleRing (@NumberField.RingOfIntegers F inst)
                        (@NumberField.instCommRingRingOfIntegers F inst)
                        (@NumberField.RingOfIntegers.instIsDedekindDomain F inst inst_1) F inst
                        (@NumberField.RingOfIntegers.instAlgebra_1 F inst)
                        (@NumberField.RingOfIntegers.instIsFractionRing F inst inst_1))))
                  (@IsDedekindDomain.FiniteAdeleRing.instAlgebra (@NumberField.RingOfIntegers F inst)
                    (@NumberField.instCommRingRingOfIntegers F inst)
                    (@NumberField.RingOfIntegers.instIsDedekindDomain F inst inst_1) F inst
                    (@NumberField.RingOfIntegers.instAlgebra_1 F inst)
                    (@NumberField.RingOfIntegers.instIsFractionRing F inst inst_1)))
                (@Algebra.toModule F E (@Semifield.toCommSemiring F (@Field.toSemifield F inst))
                  (@DivisionSemiring.toSemiring E (@Semifield.toDivisionSemiring E (@Field.toSemifield E inst_2))) inst_4))
              (@AddGroupWithOne.toAddGroup
                (@TensorProduct F (@Semifield.toCommSemiring F (@Field.toSemifield F inst))
                  (@UpperTheory.Reformulated.B.Uc13.Af F inst inst_1) E
                  (@Semiring.toAddCommMonoid (@UpperTheory.Reformulated.B.Uc13.Af F inst inst_1)
                    (@CommSemiring.toSemiring (@UpperTheory.Reformulated.B.Uc13.Af F inst inst_1)
                      (@CommRing.toCommSemiring (@UpperTheory.Reformulated.B.Uc13.Af F inst inst_1)
                        (@IsDedekindDomain.instCommRingFiniteAdeleRing (@NumberField.RingOfIntegers F inst)
                          (@NumberField.instCommRingRingOfIntegers F inst)
                          (@NumberField.RingOfIntegers.instIsDedekindDomain F inst inst_1) F inst
                          (@NumberField.RingOfIntegers.instAlgebra_1 F inst)
                          (@NumberField.RingOfIntegers.instIsFractionRing F inst inst_1)))))
                  (@Semiring.toAddCommMonoid E
                    (@DivisionSemiring.toSemiring E (@Semifield.toDivisionSemiring E (@Field.toSemifield E inst_2))))
                  (@Algebra.toModule F (@UpperTheory.Reformulated.B.Uc13.Af F inst inst_1)
                    (@Semifield.toCommSemiring F (@Field.toSemifield F inst))
                    (@CommSemiring.toSemiring (@UpperTheory.Reformulated.B.Uc13.Af F inst inst_1)
                      (@CommRing.toCommSemiring (@UpperTheory.Reformulated.B.Uc13.Af F inst inst_1)
                        (@IsDedekindDomain.instCommRingFiniteAdeleRing (@NumberField.RingOfIntegers F inst)
                          (@NumberField.instCommRingRingOfIntegers F inst)
                          (@NumberField.RingOfIntegers.instIsDedekindDomain F inst inst_1) F inst
                          (@NumberField.RingOfIntegers.instAlgebra_1 F inst)
                          (@NumberField.RingOfIntegers.instIsFractionRing F inst inst_1))))
                    (@IsDedekindDomain.FiniteAdeleRing.instAlgebra (@NumberField.RingOfIntegers F inst)
                      (@NumberField.instCommRingRingOfIntegers F inst)
                      (@NumberField.RingOfIntegers.instIsDedekindDomain F inst inst_1) F inst
                      (@NumberField.RingOfIntegers.instAlgebra_1 F inst)
                      (@NumberField.RingOfIntegers.instIsFractionRing F inst inst_1)))
                  (@Algebra.toModule F E (@Semifield.toCommSemiring F (@Field.toSemifield F inst))
                    (@DivisionSemiring.toSemiring E (@Semifield.toDivisionSemiring E (@Field.toSemifield E inst_2)))
                    inst_4))
                (@Ring.toAddGroupWithOne
                  (@TensorProduct F (@Semifield.toCommSemiring F (@Field.toSemifield F inst))
                    (@UpperTheory.Reformulated.B.Uc13.Af F inst inst_1) E
                    (@Semiring.toAddCommMonoid (@UpperTheory.Reformulated.B.Uc13.Af F inst inst_1)
                      (@CommSemiring.toSemiring (@UpperTheory.Reformulated.B.Uc13.Af F inst inst_1)
                        (@CommRing.toCommSemiring (@UpperTheory.Reformulated.B.Uc13.Af F inst inst_1)
                          (@IsDedekindDomain.instCommRingFiniteAdeleRing (@NumberField.RingOfIntegers F inst)
                            (@NumberField.instCommRingRingOfIntegers F inst)
                            (@NumberField.RingOfIntegers.instIsDedekindDomain F inst inst_1) F inst
                            (@NumberField.RingOfIntegers.instAlgebra_1 F inst)
                            (@NumberField.RingOfIntegers.instIsFractionRing F inst inst_1)))))
                    (@Semiring.toAddCommMonoid E
                      (@DivisionSemiring.toSemiring E (@Semifield.toDivisionSemiring E (@Field.toSemifield E inst_2))))
                    (@Algebra.toModule F (@UpperTheory.Reformulated.B.Uc13.Af F inst inst_1)
                      (@Semifield.toCommSemiring F (@Field.toSemifield F inst))
                      (@CommSemiring.toSemiring (@UpperTheory.Reformulated.B.Uc13.Af F inst inst_1)
                        (@CommRing.toCommSemiring (@UpperTheory.Reformulated.B.Uc13.Af F inst inst_1)
                          (@IsDedekindDomain.instCommRingFiniteAdeleRing (@NumberField.RingOfIntegers F inst)
                            (@NumberField.instCommRingRingOfIntegers F inst)
                            (@NumberField.RingOfIntegers.instIsDedekindDomain F inst inst_1) F inst
                            (@NumberField.RingOfIntegers.instAlgebra_1 F inst)
                            (@NumberField.RingOfIntegers.instIsFractionRing F inst inst_1))))
                      (@IsDedekindDomain.FiniteAdeleRing.instAlgebra (@NumberField.RingOfIntegers F inst)
                        (@NumberField.instCommRingRingOfIntegers F inst)
                        (@NumberField.RingOfIntegers.instIsDedekindDomain F inst inst_1) F inst
                        (@NumberField.RingOfIntegers.instAlgebra_1 F inst)
                        (@NumberField.RingOfIntegers.instIsFractionRing F inst inst_1)))
                    (@Algebra.toModule F E (@Semifield.toCommSemiring F (@Field.toSemifield F inst))
                      (@DivisionSemiring.toSemiring E (@Semifield.toDivisionSemiring E (@Field.toSemifield E inst_2)))
                      inst_4))
                  (@Algebra.TensorProduct.instRing F (@UpperTheory.Reformulated.B.Uc13.Af F inst inst_1) E
                    (@Semifield.toCommSemiring F (@Field.toSemifield F inst))
                    (@CommRing.toRing (@UpperTheory.Reformulated.B.Uc13.Af F inst inst_1)
                      (@IsDedekindDomain.instCommRingFiniteAdeleRing (@NumberField.RingOfIntegers F inst)
                        (@NumberField.instCommRingRingOfIntegers F inst)
                        (@NumberField.RingOfIntegers.instIsDedekindDomain F inst inst_1) F inst
                        (@NumberField.RingOfIntegers.instAlgebra_1 F inst)
                        (@NumberField.RingOfIntegers.instIsFractionRing F inst inst_1)))
                    (@IsDedekindDomain.FiniteAdeleRing.instAlgebra (@NumberField.RingOfIntegers F inst)
                      (@NumberField.instCommRingRingOfIntegers F inst)
                      (@NumberField.RingOfIntegers.instIsDedekindDomain F inst inst_1) F inst
                      (@NumberField.RingOfIntegers.instAlgebra_1 F inst)
                      (@NumberField.RingOfIntegers.instIsFractionRing F inst inst_1))
                    (@DivisionSemiring.toSemiring E (@Semifield.toDivisionSemiring E (@Field.toSemifield E inst_2)))
                    inst_4))))
            (@SetLike.instMembership
              (@AddSubgroup
                (@TensorProduct F (@Semifield.toCommSemiring F (@Field.toSemifield F inst))
                  (@UpperTheory.Reformulated.B.Uc13.Af F inst inst_1) E
                  (@Semiring.toAddCommMonoid (@UpperTheory.Reformulated.B.Uc13.Af F inst inst_1)
                    (@CommSemiring.toSemiring (@UpperTheory.Reformulated.B.Uc13.Af F inst inst_1)
                      (@CommRing.toCommSemiring (@UpperTheory.Reformulated.B.Uc13.Af F inst inst_1)
                        (@IsDedekindDomain.instCommRingFiniteAdeleRing (@NumberField.RingOfIntegers F inst)
                          (@NumberField.instCommRingRingOfIntegers F inst)
                          (@NumberField.RingOfIntegers.instIsDedekindDomain F inst inst_1) F inst
                          (@NumberField.RingOfIntegers.instAlgebra_1 F inst)
                          (@NumberField.RingOfIntegers.instIsFractionRing F inst inst_1)))))
                  (@Semiring.toAddCommMonoid E
                    (@DivisionSemiring.toSemiring E (@Semifield.toDivisionSemiring E (@Field.toSemifield E inst_2))))
                  (@Algebra.toModule F (@UpperTheory.Reformulated.B.Uc13.Af F inst inst_1)
                    (@Semifield.toCommSemiring F (@Field.toSemifield F inst))
                    (@CommSemiring.toSemiring (@UpperTheory.Reformulated.B.Uc13.Af F inst inst_1)
                      (@CommRing.toCommSemiring (@UpperTheory.Reformulated.B.Uc13.Af F inst inst_1)
                        (@IsDedekindDomain.instCommRingFiniteAdeleRing (@NumberField.RingOfIntegers F inst)
                          (@NumberField.instCommRingRingOfIntegers F inst)
                          (@NumberField.RingOfIntegers.instIsDedekindDomain F inst inst_1) F inst
                          (@NumberField.RingOfIntegers.instAlgebra_1 F inst)
                          (@NumberField.RingOfIntegers.instIsFractionRing F inst inst_1))))
                    (@IsDedekindDomain.FiniteAdeleRing.instAlgebra (@NumberField.RingOfIntegers F inst)
                      (@NumberField.instCommRingRingOfIntegers F inst)
                      (@NumberField.RingOfIntegers.instIsDedekindDomain F inst inst_1) F inst
                      (@NumberField.RingOfIntegers.instAlgebra_1 F inst)
                      (@NumberField.RingOfIntegers.instIsFractionRing F inst inst_1)))
                  (@Algebra.toModule F E (@Semifield.toCommSemiring F (@Field.toSemifield F inst))
                    (@DivisionSemiring.toSemiring E (@Semifield.toDivisionSemiring E (@Field.toSemifield E inst_2)))
                    inst_4))
                (@AddGroupWithOne.toAddGroup
                  (@TensorProduct F (@Semifield.toCommSemiring F (@Field.toSemifield F inst))
                    (@UpperTheory.Reformulated.B.Uc13.Af F inst inst_1) E
                    (@Semiring.toAddCommMonoid (@UpperTheory.Reformulated.B.Uc13.Af F inst inst_1)
                      (@CommSemiring.toSemiring (@UpperTheory.Reformulated.B.Uc13.Af F inst inst_1)
                        (@CommRing.toCommSemiring (@UpperTheory.Reformulated.B.Uc13.Af F inst inst_1)
                          (@IsDedekindDomain.instCommRingFiniteAdeleRing (@NumberField.RingOfIntegers F inst)
                            (@NumberField.instCommRingRingOfIntegers F inst)
                            (@NumberField.RingOfIntegers.instIsDedekindDomain F inst inst_1) F inst
                            (@NumberField.RingOfIntegers.instAlgebra_1 F inst)
                            (@NumberField.RingOfIntegers.instIsFractionRing F inst inst_1)))))
                    (@Semiring.toAddCommMonoid E
                      (@DivisionSemiring.toSemiring E (@Semifield.toDivisionSemiring E (@Field.toSemifield E inst_2))))
                    (@Algebra.toModule F (@UpperTheory.Reformulated.B.Uc13.Af F inst inst_1)
                      (@Semifield.toCommSemiring F (@Field.toSemifield F inst))
                      (@CommSemiring.toSemiring (@UpperTheory.Reformulated.B.Uc13.Af F inst inst_1)
                        (@CommRing.toCommSemiring (@UpperTheory.Reformulated.B.Uc13.Af F inst inst_1)
                          (@IsDedekindDomain.instCommRingFiniteAdeleRing (@NumberField.RingOfIntegers F inst)
                            (@NumberField.instCommRingRingOfIntegers F inst)
                            (@NumberField.RingOfIntegers.instIsDedekindDomain F inst inst_1) F inst
                            (@NumberField.RingOfIntegers.instAlgebra_1 F inst)
                            (@NumberField.RingOfIntegers.instIsFractionRing F inst inst_1))))
                      (@IsDedekindDomain.FiniteAdeleRing.instAlgebra (@NumberField.RingOfIntegers F inst)
                        (@NumberField.instCommRingRingOfIntegers F inst)
                        (@NumberField.RingOfIntegers.instIsDedekindDomain F inst inst_1) F inst
                        (@NumberField.RingOfIntegers.instAlgebra_1 F inst)
                        (@NumberField.RingOfIntegers.instIsFractionRing F inst inst_1)))
                    (@Algebra.toModule F E (@Semifield.toCommSemiring F (@Field.toSemifield F inst))
                      (@DivisionSemiring.toSemiring E (@Semifield.toDivisionSemiring E (@Field.toSemifield E inst_2)))
                      inst_4))
                  (@Ring.toAddGroupWithOne
                    (@TensorProduct F (@Semifield.toCommSemiring F (@Field.toSemifield F inst))
                      (@UpperTheory.Reformulated.B.Uc13.Af F inst inst_1) E
                      (@Semiring.toAddCommMonoid (@UpperTheory.Reformulated.B.Uc13.Af F inst inst_1)
                        (@CommSemiring.toSemiring (@UpperTheory.Reformulated.B.Uc13.Af F inst inst_1)
                          (@CommRing.toCommSemiring (@UpperTheory.Reformulated.B.Uc13.Af F inst inst_1)
                            (@IsDedekindDomain.instCommRingFiniteAdeleRing (@NumberField.RingOfIntegers F inst)
                              (@NumberField.instCommRingRingOfIntegers F inst)
                              (@NumberField.RingOfIntegers.instIsDedekindDomain F inst inst_1) F inst
                              (@NumberField.RingOfIntegers.instAlgebra_1 F inst)
                              (@NumberField.RingOfIntegers.instIsFractionRing F inst inst_1)))))
                      (@Semiring.toAddCommMonoid E
                        (@DivisionSemiring.toSemiring E (@Semifield.toDivisionSemiring E (@Field.toSemifield E inst_2))))
                      (@Algebra.toModule F (@UpperTheory.Reformulated.B.Uc13.Af F inst inst_1)
                        (@Semifield.toCommSemiring F (@Field.toSemifield F inst))
                        (@CommSemiring.toSemiring (@UpperTheory.Reformulated.B.Uc13.Af F inst inst_1)
                          (@CommRing.toCommSemiring (@UpperTheory.Reformulated.B.Uc13.Af F inst inst_1)
                            (@IsDedekindDomain.instCommRingFiniteAdeleRing (@NumberField.RingOfIntegers F inst)
                              (@NumberField.instCommRingRingOfIntegers F inst)
                              (@NumberField.RingOfIntegers.instIsDedekindDomain F inst inst_1) F inst
                              (@NumberField.RingOfIntegers.instAlgebra_1 F inst)
                              (@NumberField.RingOfIntegers.instIsFractionRing F inst inst_1))))
                        (@IsDedekindDomain.FiniteAdeleRing.instAlgebra (@NumberField.RingOfIntegers F inst)
                          (@NumberField.instCommRingRingOfIntegers F inst)
                          (@NumberField.RingOfIntegers.instIsDedekindDomain F inst inst_1) F inst
                          (@NumberField.RingOfIntegers.instAlgebra_1 F inst)
                          (@NumberField.RingOfIntegers.instIsFractionRing F inst inst_1)))
                      (@Algebra.toModule F E (@Semifield.toCommSemiring F (@Field.toSemifield F inst))
                        (@DivisionSemiring.toSemiring E (@Semifield.toDivisionSemiring E (@Field.toSemifield E inst_2)))
                        inst_4))
                    (@Algebra.TensorProduct.instRing F (@UpperTheory.Reformulated.B.Uc13.Af F inst inst_1) E
                      (@Semifield.toCommSemiring F (@Field.toSemifield F inst))
                      (@CommRing.toRing (@UpperTheory.Reformulated.B.Uc13.Af F inst inst_1)
                        (@IsDedekindDomain.instCommRingFiniteAdeleRing (@NumberField.RingOfIntegers F inst)
                          (@NumberField.instCommRingRingOfIntegers F inst)
                          (@NumberField.RingOfIntegers.instIsDedekindDomain F inst inst_1) F inst
                          (@NumberField.RingOfIntegers.instAlgebra_1 F inst)
                          (@NumberField.RingOfIntegers.instIsFractionRing F inst inst_1)))
                      (@IsDedekindDomain.FiniteAdeleRing.instAlgebra (@NumberField.RingOfIntegers F inst)
                        (@NumberField.instCommRingRingOfIntegers F inst)
                        (@NumberField.RingOfIntegers.instIsDedekindDomain F inst inst_1) F inst
                        (@NumberField.RingOfIntegers.instAlgebra_1 F inst)
                        (@NumberField.RingOfIntegers.instIsFractionRing F inst inst_1))
                      (@DivisionSemiring.toSemiring E (@Semifield.toDivisionSemiring E (@Field.toSemifield E inst_2)))
                      inst_4))))
              (@TensorProduct F (@Semifield.toCommSemiring F (@Field.toSemifield F inst))
                (@UpperTheory.Reformulated.B.Uc13.Af F inst inst_1) E
                (@Semiring.toAddCommMonoid (@UpperTheory.Reformulated.B.Uc13.Af F inst inst_1)
                  (@CommSemiring.toSemiring (@UpperTheory.Reformulated.B.Uc13.Af F inst inst_1)
                    (@CommRing.toCommSemiring (@UpperTheory.Reformulated.B.Uc13.Af F inst inst_1)
                      (@IsDedekindDomain.instCommRingFiniteAdeleRing (@NumberField.RingOfIntegers F inst)
                        (@NumberField.instCommRingRingOfIntegers F inst)
                        (@NumberField.RingOfIntegers.instIsDedekindDomain F inst inst_1) F inst
                        (@NumberField.RingOfIntegers.instAlgebra_1 F inst)
                        (@NumberField.RingOfIntegers.instIsFractionRing F inst inst_1)))))
                (@Semiring.toAddCommMonoid E
                  (@DivisionSemiring.toSemiring E (@Semifield.toDivisionSemiring E (@Field.toSemifield E inst_2))))
                (@Algebra.toModule F (@UpperTheory.Reformulated.B.Uc13.Af F inst inst_1)
                  (@Semifield.toCommSemiring F (@Field.toSemifield F inst))
                  (@CommSemiring.toSemiring (@UpperTheory.Reformulated.B.Uc13.Af F inst inst_1)
                    (@CommRing.toCommSemiring (@UpperTheory.Reformulated.B.Uc13.Af F inst inst_1)
                      (@IsDedekindDomain.instCommRingFiniteAdeleRing (@NumberField.RingOfIntegers F inst)
                        (@NumberField.instCommRingRingOfIntegers F inst)
                        (@NumberField.RingOfIntegers.instIsDedekindDomain F inst inst_1) F inst
                        (@NumberField.RingOfIntegers.instAlgebra_1 F inst)
                        (@NumberField.RingOfIntegers.instIsFractionRing F inst inst_1))))
                  (@IsDedekindDomain.FiniteAdeleRing.instAlgebra (@NumberField.RingOfIntegers F inst)
                    (@NumberField.instCommRingRingOfIntegers F inst)
                    (@NumberField.RingOfIntegers.instIsDedekindDomain F inst inst_1) F inst
                    (@NumberField.RingOfIntegers.instAlgebra_1 F inst)
                    (@NumberField.RingOfIntegers.instIsFractionRing F inst inst_1)))
                (@Algebra.toModule F E (@Semifield.toCommSemiring F (@Field.toSemifield F inst))
                  (@DivisionSemiring.toSemiring E (@Semifield.toDivisionSemiring E (@Field.toSemifield E inst_2))) inst_4))
              (@AddSubgroup.instSetLike
                (@TensorProduct F (@Semifield.toCommSemiring F (@Field.toSemifield F inst))
                  (@UpperTheory.Reformulated.B.Uc13.Af F inst inst_1) E
                  (@Semiring.toAddCommMonoid (@UpperTheory.Reformulated.B.Uc13.Af F inst inst_1)
                    (@CommSemiring.toSemiring (@UpperTheory.Reformulated.B.Uc13.Af F inst inst_1)
                      (@CommRing.toCommSemiring (@UpperTheory.Reformulated.B.Uc13.Af F inst inst_1)
                        (@IsDedekindDomain.instCommRingFiniteAdeleRing (@NumberField.RingOfIntegers F inst)
                          (@NumberField.instCommRingRingOfIntegers F inst)
                          (@NumberField.RingOfIntegers.instIsDedekindDomain F inst inst_1) F inst
                          (@NumberField.RingOfIntegers.instAlgebra_1 F inst)
                          (@NumberField.RingOfIntegers.instIsFractionRing F inst inst_1)))))
                  (@Semiring.toAddCommMonoid E
                    (@DivisionSemiring.toSemiring E (@Semifield.toDivisionSemiring E (@Field.toSemifield E inst_2))))
                  (@Algebra.toModule F (@UpperTheory.Reformulated.B.Uc13.Af F inst inst_1)
                    (@Semifield.toCommSemiring F (@Field.toSemifield F inst))
                    (@CommSemiring.toSemiring (@UpperTheory.Reformulated.B.Uc13.Af F inst inst_1)
                      (@CommRing.toCommSemiring (@UpperTheory.Reformulated.B.Uc13.Af F inst inst_1)
                        (@IsDedekindDomain.instCommRingFiniteAdeleRing (@NumberField.RingOfIntegers F inst)
                          (@NumberField.instCommRingRingOfIntegers F inst)
                          (@NumberField.RingOfIntegers.instIsDedekindDomain F inst inst_1) F inst
                          (@NumberField.RingOfIntegers.instAlgebra_1 F inst)
                          (@NumberField.RingOfIntegers.instIsFractionRing F inst inst_1))))
                    (@IsDedekindDomain.FiniteAdeleRing.instAlgebra (@NumberField.RingOfIntegers F inst)
                      (@NumberField.instCommRingRingOfIntegers F inst)
                      (@NumberField.RingOfIntegers.instIsDedekindDomain F inst inst_1) F inst
                      (@NumberField.RingOfIntegers.instAlgebra_1 F inst)
                      (@NumberField.RingOfIntegers.instIsFractionRing F inst inst_1)))
                  (@Algebra.toModule F E (@Semifield.toCommSemiring F (@Field.toSemifield F inst))
                    (@DivisionSemiring.toSemiring E (@Semifield.toDivisionSemiring E (@Field.toSemifield E inst_2)))
                    inst_4))
                (@AddGroupWithOne.toAddGroup
                  (@TensorProduct F (@Semifield.toCommSemiring F (@Field.toSemifield F inst))
                    (@UpperTheory.Reformulated.B.Uc13.Af F inst inst_1) E
                    (@Semiring.toAddCommMonoid (@UpperTheory.Reformulated.B.Uc13.Af F inst inst_1)
                      (@CommSemiring.toSemiring (@UpperTheory.Reformulated.B.Uc13.Af F inst inst_1)
                        (@CommRing.toCommSemiring (@UpperTheory.Reformulated.B.Uc13.Af F inst inst_1)
                          (@IsDedekindDomain.instCommRingFiniteAdeleRing (@NumberField.RingOfIntegers F inst)
                            (@NumberField.instCommRingRingOfIntegers F inst)
                            (@NumberField.RingOfIntegers.instIsDedekindDomain F inst inst_1) F inst
                            (@NumberField.RingOfIntegers.instAlgebra_1 F inst)
                            (@NumberField.RingOfIntegers.instIsFractionRing F inst inst_1)))))
                    (@Semiring.toAddCommMonoid E
                      (@DivisionSemiring.toSemiring E (@Semifield.toDivisionSemiring E (@Field.toSemifield E inst_2))))
                    (@Algebra.toModule F (@UpperTheory.Reformulated.B.Uc13.Af F inst inst_1)
                      (@Semifield.toCommSemiring F (@Field.toSemifield F inst))
                      (@CommSemiring.toSemiring (@UpperTheory.Reformulated.B.Uc13.Af F inst inst_1)
                        (@CommRing.toCommSemiring (@UpperTheory.Reformulated.B.Uc13.Af F inst inst_1)
                          (@IsDedekindDomain.instCommRingFiniteAdeleRing (@NumberField.RingOfIntegers F inst)
                            (@NumberField.instCommRingRingOfIntegers F inst)
                            (@NumberField.RingOfIntegers.instIsDedekindDomain F inst inst_1) F inst
                            (@NumberField.RingOfIntegers.instAlgebra_1 F inst)
                            (@NumberField.RingOfIntegers.instIsFractionRing F inst inst_1))))
                      (@IsDedekindDomain.FiniteAdeleRing.instAlgebra (@NumberField.RingOfIntegers F inst)
                        (@NumberField.instCommRingRingOfIntegers F inst)
                        (@NumberField.RingOfIntegers.instIsDedekindDomain F inst inst_1) F inst
                        (@NumberField.RingOfIntegers.instAlgebra_1 F inst)
                        (@NumberField.RingOfIntegers.instIsFractionRing F inst inst_1)))
                    (@Algebra.toModule F E (@Semifield.toCommSemiring F (@Field.toSemifield F inst))
                      (@DivisionSemiring.toSemiring E (@Semifield.toDivisionSemiring E (@Field.toSemifield E inst_2)))
                      inst_4))
                  (@Ring.toAddGroupWithOne
                    (@TensorProduct F (@Semifield.toCommSemiring F (@Field.toSemifield F inst))
                      (@UpperTheory.Reformulated.B.Uc13.Af F inst inst_1) E
                      (@Semiring.toAddCommMonoid (@UpperTheory.Reformulated.B.Uc13.Af F inst inst_1)
                        (@CommSemiring.toSemiring (@UpperTheory.Reformulated.B.Uc13.Af F inst inst_1)
                          (@CommRing.toCommSemiring (@UpperTheory.Reformulated.B.Uc13.Af F inst inst_1)
                            (@IsDedekindDomain.instCommRingFiniteAdeleRing (@NumberField.RingOfIntegers F inst)
                              (@NumberField.instCommRingRingOfIntegers F inst)
                              (@NumberField.RingOfIntegers.instIsDedekindDomain F inst inst_1) F inst
                              (@NumberField.RingOfIntegers.instAlgebra_1 F inst)
                              (@NumberField.RingOfIntegers.instIsFractionRing F inst inst_1)))))
                      (@Semiring.toAddCommMonoid E
                        (@DivisionSemiring.toSemiring E (@Semifield.toDivisionSemiring E (@Field.toSemifield E inst_2))))
                      (@Algebra.toModule F (@UpperTheory.Reformulated.B.Uc13.Af F inst inst_1)
                        (@Semifield.toCommSemiring F (@Field.toSemifield F inst))
                        (@CommSemiring.toSemiring (@UpperTheory.Reformulated.B.Uc13.Af F inst inst_1)
                          (@CommRing.toCommSemiring (@UpperTheory.Reformulated.B.Uc13.Af F inst inst_1)
                            (@IsDedekindDomain.instCommRingFiniteAdeleRing (@NumberField.RingOfIntegers F inst)
                              (@NumberField.instCommRingRingOfIntegers F inst)
                              (@NumberField.RingOfIntegers.instIsDedekindDomain F inst inst_1) F inst
                              (@NumberField.RingOfIntegers.instAlgebra_1 F inst)
                              (@NumberField.RingOfIntegers.instIsFractionRing F inst inst_1))))
                        (@IsDedekindDomain.FiniteAdeleRing.instAlgebra (@NumberField.RingOfIntegers F inst)
                          (@NumberField.instCommRingRingOfIntegers F inst)
                          (@NumberField.RingOfIntegers.instIsDedekindDomain F inst inst_1) F inst
                          (@NumberField.RingOfIntegers.instAlgebra_1 F inst)
                          (@NumberField.RingOfIntegers.instIsFractionRing F inst inst_1)))
                      (@Algebra.toModule F E (@Semifield.toCommSemiring F (@Field.toSemifield F inst))
                        (@DivisionSemiring.toSemiring E (@Semifield.toDivisionSemiring E (@Field.toSemifield E inst_2)))
                        inst_4))
                    (@Algebra.TensorProduct.instRing F (@UpperTheory.Reformulated.B.Uc13.Af F inst inst_1) E
                      (@Semifield.toCommSemiring F (@Field.toSemifield F inst))
                      (@CommRing.toRing (@UpperTheory.Reformulated.B.Uc13.Af F inst inst_1)
                        (@IsDedekindDomain.instCommRingFiniteAdeleRing (@NumberField.RingOfIntegers F inst)
                          (@NumberField.instCommRingRingOfIntegers F inst)
                          (@NumberField.RingOfIntegers.instIsDedekindDomain F inst inst_1) F inst
                          (@NumberField.RingOfIntegers.instAlgebra_1 F inst)
                          (@NumberField.RingOfIntegers.instIsFractionRing F inst inst_1)))
                      (@IsDedekindDomain.FiniteAdeleRing.instAlgebra (@NumberField.RingOfIntegers F inst)
                        (@NumberField.instCommRingRingOfIntegers F inst)
                        (@NumberField.RingOfIntegers.instIsDedekindDomain F inst inst_1) F inst
                        (@NumberField.RingOfIntegers.instAlgebra_1 F inst)
                        (@NumberField.RingOfIntegers.instIsFractionRing F inst inst_1))
                      (@DivisionSemiring.toSemiring E (@Semifield.toDivisionSemiring E (@Field.toSemifield E inst_2)))
                      inst_4)))))
            (@UpperTheory.Reformulated.B.Uc13.intA F E inst inst_1 inst_2 inst_4) y →
          @Membership.mem
            (@TensorProduct F (@Semifield.toCommSemiring F (@Field.toSemifield F inst)) (@UpperTheory.Reformulated.B.Uc13.Af F inst inst_1)
              E
              (@Semiring.toAddCommMonoid (@UpperTheory.Reformulated.B.Uc13.Af F inst inst_1)
                (@CommSemiring.toSemiring (@UpperTheory.Reformulated.B.Uc13.Af F inst inst_1)
                  (@CommRing.toCommSemiring (@UpperTheory.Reformulated.B.Uc13.Af F inst inst_1)
                    (@IsDedekindDomain.instCommRingFiniteAdeleRing (@NumberField.RingOfIntegers F inst)
                      (@NumberField.instCommRingRingOfIntegers F inst)
                      (@NumberField.RingOfIntegers.instIsDedekindDomain F inst inst_1) F inst
                      (@NumberField.RingOfIntegers.instAlgebra_1 F inst)
                      (@NumberField.RingOfIntegers.instIsFractionRing F inst inst_1)))))
              (@Semiring.toAddCommMonoid E
                (@DivisionSemiring.toSemiring E (@Semifield.toDivisionSemiring E (@Field.toSemifield E inst_2))))
              (@Algebra.toModule F (@UpperTheory.Reformulated.B.Uc13.Af F inst inst_1)
                (@Semifield.toCommSemiring F (@Field.toSemifield F inst))
                (@CommSemiring.toSemiring (@UpperTheory.Reformulated.B.Uc13.Af F inst inst_1)
                  (@CommRing.toCommSemiring (@UpperTheory.Reformulated.B.Uc13.Af F inst inst_1)
                    (@IsDedekindDomain.instCommRingFiniteAdeleRing (@NumberField.RingOfIntegers F inst)
                      (@NumberField.instCommRingRingOfIntegers F inst)
                      (@NumberField.RingOfIntegers.instIsDedekindDomain F inst inst_1) F inst
                      (@NumberField.RingOfIntegers.instAlgebra_1 F inst)
                      (@NumberField.RingOfIntegers.instIsFractionRing F inst inst_1))))
                (@IsDedekindDomain.FiniteAdeleRing.instAlgebra (@NumberField.RingOfIntegers F inst)
                  (@NumberField.instCommRingRingOfIntegers F inst)
                  (@NumberField.RingOfIntegers.instIsDedekindDomain F inst inst_1) F inst
                  (@NumberField.RingOfIntegers.instAlgebra_1 F inst)
                  (@NumberField.RingOfIntegers.instIsFractionRing F inst inst_1)))
              (@Algebra.toModule F E (@Semifield.toCommSemiring F (@Field.toSemifield F inst))
                (@DivisionSemiring.toSemiring E (@Semifield.toDivisionSemiring E (@Field.toSemifield E inst_2))) inst_4))
            (@AddSubgroup
              (@TensorProduct F (@Semifield.toCommSemiring F (@Field.toSemifield F inst))
                (@UpperTheory.Reformulated.B.Uc13.Af F inst inst_1) E
                (@Semiring.toAddCommMonoid (@UpperTheory.Reformulated.B.Uc13.Af F inst inst_1)
                  (@CommSemiring.toSemiring (@UpperTheory.Reformulated.B.Uc13.Af F inst inst_1)
                    (@CommRing.toCommSemiring (@UpperTheory.Reformulated.B.Uc13.Af F inst inst_1)
                      (@IsDedekindDomain.instCommRingFiniteAdeleRing (@NumberField.RingOfIntegers F inst)
                        (@NumberField.instCommRingRingOfIntegers F inst)
                        (@NumberField.RingOfIntegers.instIsDedekindDomain F inst inst_1) F inst
                        (@NumberField.RingOfIntegers.instAlgebra_1 F inst)
                        (@NumberField.RingOfIntegers.instIsFractionRing F inst inst_1)))))
                (@Semiring.toAddCommMonoid E
                  (@DivisionSemiring.toSemiring E (@Semifield.toDivisionSemiring E (@Field.toSemifield E inst_2))))
                (@Algebra.toModule F (@UpperTheory.Reformulated.B.Uc13.Af F inst inst_1)
                  (@Semifield.toCommSemiring F (@Field.toSemifield F inst))
                  (@CommSemiring.toSemiring (@UpperTheory.Reformulated.B.Uc13.Af F inst inst_1)
                    (@CommRing.toCommSemiring (@UpperTheory.Reformulated.B.Uc13.Af F inst inst_1)
                      (@IsDedekindDomain.instCommRingFiniteAdeleRing (@NumberField.RingOfIntegers F inst)
                        (@NumberField.instCommRingRingOfIntegers F inst)
                        (@NumberField.RingOfIntegers.instIsDedekindDomain F inst inst_1) F inst
                        (@NumberField.RingOfIntegers.instAlgebra_1 F inst)
                        (@NumberField.RingOfIntegers.instIsFractionRing F inst inst_1))))
                  (@IsDedekindDomain.FiniteAdeleRing.instAlgebra (@NumberField.RingOfIntegers F inst)
                    (@NumberField.instCommRingRingOfIntegers F inst)
                    (@NumberField.RingOfIntegers.instIsDedekindDomain F inst inst_1) F inst
                    (@NumberField.RingOfIntegers.instAlgebra_1 F inst)
                    (@NumberField.RingOfIntegers.instIsFractionRing F inst inst_1)))
                (@Algebra.toModule F E (@Semifield.toCommSemiring F (@Field.toSemifield F inst))
                  (@DivisionSemiring.toSemiring E (@Semifield.toDivisionSemiring E (@Field.toSemifield E inst_2))) inst_4))
              (@AddGroupWithOne.toAddGroup
                (@TensorProduct F (@Semifield.toCommSemiring F (@Field.toSemifield F inst))
                  (@UpperTheory.Reformulated.B.Uc13.Af F inst inst_1) E
                  (@Semiring.toAddCommMonoid (@UpperTheory.Reformulated.B.Uc13.Af F inst inst_1)
                    (@CommSemiring.toSemiring (@UpperTheory.Reformulated.B.Uc13.Af F inst inst_1)
                      (@CommRing.toCommSemiring (@UpperTheory.Reformulated.B.Uc13.Af F inst inst_1)
                        (@IsDedekindDomain.instCommRingFiniteAdeleRing (@NumberField.RingOfIntegers F inst)
                          (@NumberField.instCommRingRingOfIntegers F inst)
                          (@NumberField.RingOfIntegers.instIsDedekindDomain F inst inst_1) F inst
                          (@NumberField.RingOfIntegers.instAlgebra_1 F inst)
                          (@NumberField.RingOfIntegers.instIsFractionRing F inst inst_1)))))
                  (@Semiring.toAddCommMonoid E
                    (@DivisionSemiring.toSemiring E (@Semifield.toDivisionSemiring E (@Field.toSemifield E inst_2))))
                  (@Algebra.toModule F (@UpperTheory.Reformulated.B.Uc13.Af F inst inst_1)
                    (@Semifield.toCommSemiring F (@Field.toSemifield F inst))
                    (@CommSemiring.toSemiring (@UpperTheory.Reformulated.B.Uc13.Af F inst inst_1)
                      (@CommRing.toCommSemiring (@UpperTheory.Reformulated.B.Uc13.Af F inst inst_1)
                        (@IsDedekindDomain.instCommRingFiniteAdeleRing (@NumberField.RingOfIntegers F inst)
                          (@NumberField.instCommRingRingOfIntegers F inst)
                          (@NumberField.RingOfIntegers.instIsDedekindDomain F inst inst_1) F inst
                          (@NumberField.RingOfIntegers.instAlgebra_1 F inst)
                          (@NumberField.RingOfIntegers.instIsFractionRing F inst inst_1))))
                    (@IsDedekindDomain.FiniteAdeleRing.instAlgebra (@NumberField.RingOfIntegers F inst)
                      (@NumberField.instCommRingRingOfIntegers F inst)
                      (@NumberField.RingOfIntegers.instIsDedekindDomain F inst inst_1) F inst
                      (@NumberField.RingOfIntegers.instAlgebra_1 F inst)
                      (@NumberField.RingOfIntegers.instIsFractionRing F inst inst_1)))
                  (@Algebra.toModule F E (@Semifield.toCommSemiring F (@Field.toSemifield F inst))
                    (@DivisionSemiring.toSemiring E (@Semifield.toDivisionSemiring E (@Field.toSemifield E inst_2)))
                    inst_4))
                (@Ring.toAddGroupWithOne
                  (@TensorProduct F (@Semifield.toCommSemiring F (@Field.toSemifield F inst))
                    (@UpperTheory.Reformulated.B.Uc13.Af F inst inst_1) E
                    (@Semiring.toAddCommMonoid (@UpperTheory.Reformulated.B.Uc13.Af F inst inst_1)
                      (@CommSemiring.toSemiring (@UpperTheory.Reformulated.B.Uc13.Af F inst inst_1)
                        (@CommRing.toCommSemiring (@UpperTheory.Reformulated.B.Uc13.Af F inst inst_1)
                          (@IsDedekindDomain.instCommRingFiniteAdeleRing (@NumberField.RingOfIntegers F inst)
                            (@NumberField.instCommRingRingOfIntegers F inst)
                            (@NumberField.RingOfIntegers.instIsDedekindDomain F inst inst_1) F inst
                            (@NumberField.RingOfIntegers.instAlgebra_1 F inst)
                            (@NumberField.RingOfIntegers.instIsFractionRing F inst inst_1)))))
                    (@Semiring.toAddCommMonoid E
                      (@DivisionSemiring.toSemiring E (@Semifield.toDivisionSemiring E (@Field.toSemifield E inst_2))))
                    (@Algebra.toModule F (@UpperTheory.Reformulated.B.Uc13.Af F inst inst_1)
                      (@Semifield.toCommSemiring F (@Field.toSemifield F inst))
                      (@CommSemiring.toSemiring (@UpperTheory.Reformulated.B.Uc13.Af F inst inst_1)
                        (@CommRing.toCommSemiring (@UpperTheory.Reformulated.B.Uc13.Af F inst inst_1)
                          (@IsDedekindDomain.instCommRingFiniteAdeleRing (@NumberField.RingOfIntegers F inst)
                            (@NumberField.instCommRingRingOfIntegers F inst)
                            (@NumberField.RingOfIntegers.instIsDedekindDomain F inst inst_1) F inst
                            (@NumberField.RingOfIntegers.instAlgebra_1 F inst)
                            (@NumberField.RingOfIntegers.instIsFractionRing F inst inst_1))))
                      (@IsDedekindDomain.FiniteAdeleRing.instAlgebra (@NumberField.RingOfIntegers F inst)
                        (@NumberField.instCommRingRingOfIntegers F inst)
                        (@NumberField.RingOfIntegers.instIsDedekindDomain F inst inst_1) F inst
                        (@NumberField.RingOfIntegers.instAlgebra_1 F inst)
                        (@NumberField.RingOfIntegers.instIsFractionRing F inst inst_1)))
                    (@Algebra.toModule F E (@Semifield.toCommSemiring F (@Field.toSemifield F inst))
                      (@DivisionSemiring.toSemiring E (@Semifield.toDivisionSemiring E (@Field.toSemifield E inst_2)))
                      inst_4))
                  (@Algebra.TensorProduct.instRing F (@UpperTheory.Reformulated.B.Uc13.Af F inst inst_1) E
                    (@Semifield.toCommSemiring F (@Field.toSemifield F inst))
                    (@CommRing.toRing (@UpperTheory.Reformulated.B.Uc13.Af F inst inst_1)
                      (@IsDedekindDomain.instCommRingFiniteAdeleRing (@NumberField.RingOfIntegers F inst)
                        (@NumberField.instCommRingRingOfIntegers F inst)
                        (@NumberField.RingOfIntegers.instIsDedekindDomain F inst inst_1) F inst
                        (@NumberField.RingOfIntegers.instAlgebra_1 F inst)
                        (@NumberField.RingOfIntegers.instIsFractionRing F inst inst_1)))
                    (@IsDedekindDomain.FiniteAdeleRing.instAlgebra (@NumberField.RingOfIntegers F inst)
                      (@NumberField.instCommRingRingOfIntegers F inst)
                      (@NumberField.RingOfIntegers.instIsDedekindDomain F inst inst_1) F inst
                      (@NumberField.RingOfIntegers.instAlgebra_1 F inst)
                      (@NumberField.RingOfIntegers.instIsFractionRing F inst inst_1))
                    (@DivisionSemiring.toSemiring E (@Semifield.toDivisionSemiring E (@Field.toSemifield E inst_2)))
                    inst_4))))
            (@SetLike.instMembership
              (@AddSubgroup
                (@TensorProduct F (@Semifield.toCommSemiring F (@Field.toSemifield F inst))
                  (@UpperTheory.Reformulated.B.Uc13.Af F inst inst_1) E
                  (@Semiring.toAddCommMonoid (@UpperTheory.Reformulated.B.Uc13.Af F inst inst_1)
                    (@CommSemiring.toSemiring (@UpperTheory.Reformulated.B.Uc13.Af F inst inst_1)
                      (@CommRing.toCommSemiring (@UpperTheory.Reformulated.B.Uc13.Af F inst inst_1)
                        (@IsDedekindDomain.instCommRingFiniteAdeleRing (@NumberField.RingOfIntegers F inst)
                          (@NumberField.instCommRingRingOfIntegers F inst)
                          (@NumberField.RingOfIntegers.instIsDedekindDomain F inst inst_1) F inst
                          (@NumberField.RingOfIntegers.instAlgebra_1 F inst)
                          (@NumberField.RingOfIntegers.instIsFractionRing F inst inst_1)))))
                  (@Semiring.toAddCommMonoid E
                    (@DivisionSemiring.toSemiring E (@Semifield.toDivisionSemiring E (@Field.toSemifield E inst_2))))
                  (@Algebra.toModule F (@UpperTheory.Reformulated.B.Uc13.Af F inst inst_1)
                    (@Semifield.toCommSemiring F (@Field.toSemifield F inst))
                    (@CommSemiring.toSemiring (@UpperTheory.Reformulated.B.Uc13.Af F inst inst_1)
                      (@CommRing.toCommSemiring (@UpperTheory.Reformulated.B.Uc13.Af F inst inst_1)
                        (@IsDedekindDomain.instCommRingFiniteAdeleRing (@NumberField.RingOfIntegers F inst)
                          (@NumberField.instCommRingRingOfIntegers F inst)
                          (@NumberField.RingOfIntegers.instIsDedekindDomain F inst inst_1) F inst
                          (@NumberField.RingOfIntegers.instAlgebra_1 F inst)
                          (@NumberField.RingOfIntegers.instIsFractionRing F inst inst_1))))
                    (@IsDedekindDomain.FiniteAdeleRing.instAlgebra (@NumberField.RingOfIntegers F inst)
                      (@NumberField.instCommRingRingOfIntegers F inst)
                      (@NumberField.RingOfIntegers.instIsDedekindDomain F inst inst_1) F inst
                      (@NumberField.RingOfIntegers.instAlgebra_1 F inst)
                      (@NumberField.RingOfIntegers.instIsFractionRing F inst inst_1)))
                  (@Algebra.toModule F E (@Semifield.toCommSemiring F (@Field.toSemifield F inst))
                    (@DivisionSemiring.toSemiring E (@Semifield.toDivisionSemiring E (@Field.toSemifield E inst_2)))
                    inst_4))
                (@AddGroupWithOne.toAddGroup
                  (@TensorProduct F (@Semifield.toCommSemiring F (@Field.toSemifield F inst))
                    (@UpperTheory.Reformulated.B.Uc13.Af F inst inst_1) E
                    (@Semiring.toAddCommMonoid (@UpperTheory.Reformulated.B.Uc13.Af F inst inst_1)
                      (@CommSemiring.toSemiring (@UpperTheory.Reformulated.B.Uc13.Af F inst inst_1)
                        (@CommRing.toCommSemiring (@UpperTheory.Reformulated.B.Uc13.Af F inst inst_1)
                          (@IsDedekindDomain.instCommRingFiniteAdeleRing (@NumberField.RingOfIntegers F inst)
                            (@NumberField.instCommRingRingOfIntegers F inst)
                            (@NumberField.RingOfIntegers.instIsDedekindDomain F inst inst_1) F inst
                            (@NumberField.RingOfIntegers.instAlgebra_1 F inst)
                            (@NumberField.RingOfIntegers.instIsFractionRing F inst inst_1)))))
                    (@Semiring.toAddCommMonoid E
                      (@DivisionSemiring.toSemiring E (@Semifield.toDivisionSemiring E (@Field.toSemifield E inst_2))))
                    (@Algebra.toModule F (@UpperTheory.Reformulated.B.Uc13.Af F inst inst_1)
                      (@Semifield.toCommSemiring F (@Field.toSemifield F inst))
                      (@CommSemiring.toSemiring (@UpperTheory.Reformulated.B.Uc13.Af F inst inst_1)
                        (@CommRing.toCommSemiring (@UpperTheory.Reformulated.B.Uc13.Af F inst inst_1)
                          (@IsDedekindDomain.instCommRingFiniteAdeleRing (@NumberField.RingOfIntegers F inst)
                            (@NumberField.instCommRingRingOfIntegers F inst)
                            (@NumberField.RingOfIntegers.instIsDedekindDomain F inst inst_1) F inst
                            (@NumberField.RingOfIntegers.instAlgebra_1 F inst)
                            (@NumberField.RingOfIntegers.instIsFractionRing F inst inst_1))))
                      (@IsDedekindDomain.FiniteAdeleRing.instAlgebra (@NumberField.RingOfIntegers F inst)
                        (@NumberField.instCommRingRingOfIntegers F inst)
                        (@NumberField.RingOfIntegers.instIsDedekindDomain F inst inst_1) F inst
                        (@NumberField.RingOfIntegers.instAlgebra_1 F inst)
                        (@NumberField.RingOfIntegers.instIsFractionRing F inst inst_1)))
                    (@Algebra.toModule F E (@Semifield.toCommSemiring F (@Field.toSemifield F inst))
                      (@DivisionSemiring.toSemiring E (@Semifield.toDivisionSemiring E (@Field.toSemifield E inst_2)))
                      inst_4))
                  (@Ring.toAddGroupWithOne
                    (@TensorProduct F (@Semifield.toCommSemiring F (@Field.toSemifield F inst))
                      (@UpperTheory.Reformulated.B.Uc13.Af F inst inst_1) E
                      (@Semiring.toAddCommMonoid (@UpperTheory.Reformulated.B.Uc13.Af F inst inst_1)
                        (@CommSemiring.toSemiring (@UpperTheory.Reformulated.B.Uc13.Af F inst inst_1)
                          (@CommRing.toCommSemiring (@UpperTheory.Reformulated.B.Uc13.Af F inst inst_1)
                            (@IsDedekindDomain.instCommRingFiniteAdeleRing (@NumberField.RingOfIntegers F inst)
                              (@NumberField.instCommRingRingOfIntegers F inst)
                              (@NumberField.RingOfIntegers.instIsDedekindDomain F inst inst_1) F inst
                              (@NumberField.RingOfIntegers.instAlgebra_1 F inst)
                              (@NumberField.RingOfIntegers.instIsFractionRing F inst inst_1)))))
                      (@Semiring.toAddCommMonoid E
                        (@DivisionSemiring.toSemiring E (@Semifield.toDivisionSemiring E (@Field.toSemifield E inst_2))))
                      (@Algebra.toModule F (@UpperTheory.Reformulated.B.Uc13.Af F inst inst_1)
                        (@Semifield.toCommSemiring F (@Field.toSemifield F inst))
                        (@CommSemiring.toSemiring (@UpperTheory.Reformulated.B.Uc13.Af F inst inst_1)
                          (@CommRing.toCommSemiring (@UpperTheory.Reformulated.B.Uc13.Af F inst inst_1)
                            (@IsDedekindDomain.instCommRingFiniteAdeleRing (@NumberField.RingOfIntegers F inst)
                              (@NumberField.instCommRingRingOfIntegers F inst)
                              (@NumberField.RingOfIntegers.instIsDedekindDomain F inst inst_1) F inst
                              (@NumberField.RingOfIntegers.instAlgebra_1 F inst)
                              (@NumberField.RingOfIntegers.instIsFractionRing F inst inst_1))))
                        (@IsDedekindDomain.FiniteAdeleRing.instAlgebra (@NumberField.RingOfIntegers F inst)
                          (@NumberField.instCommRingRingOfIntegers F inst)
                          (@NumberField.RingOfIntegers.instIsDedekindDomain F inst inst_1) F inst
                          (@NumberField.RingOfIntegers.instAlgebra_1 F inst)
                          (@NumberField.RingOfIntegers.instIsFractionRing F inst inst_1)))
                      (@Algebra.toModule F E (@Semifield.toCommSemiring F (@Field.toSemifield F inst))
                        (@DivisionSemiring.toSemiring E (@Semifield.toDivisionSemiring E (@Field.toSemifield E inst_2)))
                        inst_4))
                    (@Algebra.TensorProduct.instRing F (@UpperTheory.Reformulated.B.Uc13.Af F inst inst_1) E
                      (@Semifield.toCommSemiring F (@Field.toSemifield F inst))
                      (@CommRing.toRing (@UpperTheory.Reformulated.B.Uc13.Af F inst inst_1)
                        (@IsDedekindDomain.instCommRingFiniteAdeleRing (@NumberField.RingOfIntegers F inst)
                          (@NumberField.instCommRingRingOfIntegers F inst)
                          (@NumberField.RingOfIntegers.instIsDedekindDomain F inst inst_1) F inst
                          (@NumberField.RingOfIntegers.instAlgebra_1 F inst)
                          (@NumberField.RingOfIntegers.instIsFractionRing F inst inst_1)))
                      (@IsDedekindDomain.FiniteAdeleRing.instAlgebra (@NumberField.RingOfIntegers F inst)
                        (@NumberField.instCommRingRingOfIntegers F inst)
                        (@NumberField.RingOfIntegers.instIsDedekindDomain F inst inst_1) F inst
                        (@NumberField.RingOfIntegers.instAlgebra_1 F inst)
                        (@NumberField.RingOfIntegers.instIsFractionRing F inst inst_1))
                      (@DivisionSemiring.toSemiring E (@Semifield.toDivisionSemiring E (@Field.toSemifield E inst_2)))
                      inst_4))))
              (@TensorProduct F (@Semifield.toCommSemiring F (@Field.toSemifield F inst))
                (@UpperTheory.Reformulated.B.Uc13.Af F inst inst_1) E
                (@Semiring.toAddCommMonoid (@UpperTheory.Reformulated.B.Uc13.Af F inst inst_1)
                  (@CommSemiring.toSemiring (@UpperTheory.Reformulated.B.Uc13.Af F inst inst_1)
                    (@CommRing.toCommSemiring (@UpperTheory.Reformulated.B.Uc13.Af F inst inst_1)
                      (@IsDedekindDomain.instCommRingFiniteAdeleRing (@NumberField.RingOfIntegers F inst)
                        (@NumberField.instCommRingRingOfIntegers F inst)
                        (@NumberField.RingOfIntegers.instIsDedekindDomain F inst inst_1) F inst
                        (@NumberField.RingOfIntegers.instAlgebra_1 F inst)
                        (@NumberField.RingOfIntegers.instIsFractionRing F inst inst_1)))))
                (@Semiring.toAddCommMonoid E
                  (@DivisionSemiring.toSemiring E (@Semifield.toDivisionSemiring E (@Field.toSemifield E inst_2))))
                (@Algebra.toModule F (@UpperTheory.Reformulated.B.Uc13.Af F inst inst_1)
                  (@Semifield.toCommSemiring F (@Field.toSemifield F inst))
                  (@CommSemiring.toSemiring (@UpperTheory.Reformulated.B.Uc13.Af F inst inst_1)
                    (@CommRing.toCommSemiring (@UpperTheory.Reformulated.B.Uc13.Af F inst inst_1)
                      (@IsDedekindDomain.instCommRingFiniteAdeleRing (@NumberField.RingOfIntegers F inst)
                        (@NumberField.instCommRingRingOfIntegers F inst)
                        (@NumberField.RingOfIntegers.instIsDedekindDomain F inst inst_1) F inst
                        (@NumberField.RingOfIntegers.instAlgebra_1 F inst)
                        (@NumberField.RingOfIntegers.instIsFractionRing F inst inst_1))))
                  (@IsDedekindDomain.FiniteAdeleRing.instAlgebra (@NumberField.RingOfIntegers F inst)
                    (@NumberField.instCommRingRingOfIntegers F inst)
                    (@NumberField.RingOfIntegers.instIsDedekindDomain F inst inst_1) F inst
                    (@NumberField.RingOfIntegers.instAlgebra_1 F inst)
                    (@NumberField.RingOfIntegers.instIsFractionRing F inst inst_1)))
                (@Algebra.toModule F E (@Semifield.toCommSemiring F (@Field.toSemifield F inst))
                  (@DivisionSemiring.toSemiring E (@Semifield.toDivisionSemiring E (@Field.toSemifield E inst_2))) inst_4))
              (@AddSubgroup.instSetLike
                (@TensorProduct F (@Semifield.toCommSemiring F (@Field.toSemifield F inst))
                  (@UpperTheory.Reformulated.B.Uc13.Af F inst inst_1) E
                  (@Semiring.toAddCommMonoid (@UpperTheory.Reformulated.B.Uc13.Af F inst inst_1)
                    (@CommSemiring.toSemiring (@UpperTheory.Reformulated.B.Uc13.Af F inst inst_1)
                      (@CommRing.toCommSemiring (@UpperTheory.Reformulated.B.Uc13.Af F inst inst_1)
                        (@IsDedekindDomain.instCommRingFiniteAdeleRing (@NumberField.RingOfIntegers F inst)
                          (@NumberField.instCommRingRingOfIntegers F inst)
                          (@NumberField.RingOfIntegers.instIsDedekindDomain F inst inst_1) F inst
                          (@NumberField.RingOfIntegers.instAlgebra_1 F inst)
                          (@NumberField.RingOfIntegers.instIsFractionRing F inst inst_1)))))
                  (@Semiring.toAddCommMonoid E
                    (@DivisionSemiring.toSemiring E (@Semifield.toDivisionSemiring E (@Field.toSemifield E inst_2))))
                  (@Algebra.toModule F (@UpperTheory.Reformulated.B.Uc13.Af F inst inst_1)
                    (@Semifield.toCommSemiring F (@Field.toSemifield F inst))
                    (@CommSemiring.toSemiring (@UpperTheory.Reformulated.B.Uc13.Af F inst inst_1)
                      (@CommRing.toCommSemiring (@UpperTheory.Reformulated.B.Uc13.Af F inst inst_1)
                        (@IsDedekindDomain.instCommRingFiniteAdeleRing (@NumberField.RingOfIntegers F inst)
                          (@NumberField.instCommRingRingOfIntegers F inst)
                          (@NumberField.RingOfIntegers.instIsDedekindDomain F inst inst_1) F inst
                          (@NumberField.RingOfIntegers.instAlgebra_1 F inst)
                          (@NumberField.RingOfIntegers.instIsFractionRing F inst inst_1))))
                    (@IsDedekindDomain.FiniteAdeleRing.instAlgebra (@NumberField.RingOfIntegers F inst)
                      (@NumberField.instCommRingRingOfIntegers F inst)
                      (@NumberField.RingOfIntegers.instIsDedekindDomain F inst inst_1) F inst
                      (@NumberField.RingOfIntegers.instAlgebra_1 F inst)
                      (@NumberField.RingOfIntegers.instIsFractionRing F inst inst_1)))
                  (@Algebra.toModule F E (@Semifield.toCommSemiring F (@Field.toSemifield F inst))
                    (@DivisionSemiring.toSemiring E (@Semifield.toDivisionSemiring E (@Field.toSemifield E inst_2)))
                    inst_4))
                (@AddGroupWithOne.toAddGroup
                  (@TensorProduct F (@Semifield.toCommSemiring F (@Field.toSemifield F inst))
                    (@UpperTheory.Reformulated.B.Uc13.Af F inst inst_1) E
                    (@Semiring.toAddCommMonoid (@UpperTheory.Reformulated.B.Uc13.Af F inst inst_1)
                      (@CommSemiring.toSemiring (@UpperTheory.Reformulated.B.Uc13.Af F inst inst_1)
                        (@CommRing.toCommSemiring (@UpperTheory.Reformulated.B.Uc13.Af F inst inst_1)
                          (@IsDedekindDomain.instCommRingFiniteAdeleRing (@NumberField.RingOfIntegers F inst)
                            (@NumberField.instCommRingRingOfIntegers F inst)
                            (@NumberField.RingOfIntegers.instIsDedekindDomain F inst inst_1) F inst
                            (@NumberField.RingOfIntegers.instAlgebra_1 F inst)
                            (@NumberField.RingOfIntegers.instIsFractionRing F inst inst_1)))))
                    (@Semiring.toAddCommMonoid E
                      (@DivisionSemiring.toSemiring E (@Semifield.toDivisionSemiring E (@Field.toSemifield E inst_2))))
                    (@Algebra.toModule F (@UpperTheory.Reformulated.B.Uc13.Af F inst inst_1)
                      (@Semifield.toCommSemiring F (@Field.toSemifield F inst))
                      (@CommSemiring.toSemiring (@UpperTheory.Reformulated.B.Uc13.Af F inst inst_1)
                        (@CommRing.toCommSemiring (@UpperTheory.Reformulated.B.Uc13.Af F inst inst_1)
                          (@IsDedekindDomain.instCommRingFiniteAdeleRing (@NumberField.RingOfIntegers F inst)
                            (@NumberField.instCommRingRingOfIntegers F inst)
                            (@NumberField.RingOfIntegers.instIsDedekindDomain F inst inst_1) F inst
                            (@NumberField.RingOfIntegers.instAlgebra_1 F inst)
                            (@NumberField.RingOfIntegers.instIsFractionRing F inst inst_1))))
                      (@IsDedekindDomain.FiniteAdeleRing.instAlgebra (@NumberField.RingOfIntegers F inst)
                        (@NumberField.instCommRingRingOfIntegers F inst)
                        (@NumberField.RingOfIntegers.instIsDedekindDomain F inst inst_1) F inst
                        (@NumberField.RingOfIntegers.instAlgebra_1 F inst)
                        (@NumberField.RingOfIntegers.instIsFractionRing F inst inst_1)))
                    (@Algebra.toModule F E (@Semifield.toCommSemiring F (@Field.toSemifield F inst))
                      (@DivisionSemiring.toSemiring E (@Semifield.toDivisionSemiring E (@Field.toSemifield E inst_2)))
                      inst_4))
                  (@Ring.toAddGroupWithOne
                    (@TensorProduct F (@Semifield.toCommSemiring F (@Field.toSemifield F inst))
                      (@UpperTheory.Reformulated.B.Uc13.Af F inst inst_1) E
                      (@Semiring.toAddCommMonoid (@UpperTheory.Reformulated.B.Uc13.Af F inst inst_1)
                        (@CommSemiring.toSemiring (@UpperTheory.Reformulated.B.Uc13.Af F inst inst_1)
                          (@CommRing.toCommSemiring (@UpperTheory.Reformulated.B.Uc13.Af F inst inst_1)
                            (@IsDedekindDomain.instCommRingFiniteAdeleRing (@NumberField.RingOfIntegers F inst)
                              (@NumberField.instCommRingRingOfIntegers F inst)
                              (@NumberField.RingOfIntegers.instIsDedekindDomain F inst inst_1) F inst
                              (@NumberField.RingOfIntegers.instAlgebra_1 F inst)
                              (@NumberField.RingOfIntegers.instIsFractionRing F inst inst_1)))))
                      (@Semiring.toAddCommMonoid E
                        (@DivisionSemiring.toSemiring E (@Semifield.toDivisionSemiring E (@Field.toSemifield E inst_2))))
                      (@Algebra.toModule F (@UpperTheory.Reformulated.B.Uc13.Af F inst inst_1)
                        (@Semifield.toCommSemiring F (@Field.toSemifield F inst))
                        (@CommSemiring.toSemiring (@UpperTheory.Reformulated.B.Uc13.Af F inst inst_1)
                          (@CommRing.toCommSemiring (@UpperTheory.Reformulated.B.Uc13.Af F inst inst_1)
                            (@IsDedekindDomain.instCommRingFiniteAdeleRing (@NumberField.RingOfIntegers F inst)
                              (@NumberField.instCommRingRingOfIntegers F inst)
                              (@NumberField.RingOfIntegers.instIsDedekindDomain F inst inst_1) F inst
                              (@NumberField.RingOfIntegers.instAlgebra_1 F inst)
                              (@NumberField.RingOfIntegers.instIsFractionRing F inst inst_1))))
                        (@IsDedekindDomain.FiniteAdeleRing.instAlgebra (@NumberField.RingOfIntegers F inst)
                          (@NumberField.instCommRingRingOfIntegers F inst)
                          (@NumberField.RingOfIntegers.instIsDedekindDomain F inst inst_1) F inst
                          (@NumberField.RingOfIntegers.instAlgebra_1 F inst)
                          (@NumberField.RingOfIntegers.instIsFractionRing F inst inst_1)))
                      (@Algebra.toModule F E (@Semifield.toCommSemiring F (@Field.toSemifield F inst))
                        (@DivisionSemiring.toSemiring E (@Semifield.toDivisionSemiring E (@Field.toSemifield E inst_2)))
                        inst_4))
                    (@Algebra.TensorProduct.instRing F (@UpperTheory.Reformulated.B.Uc13.Af F inst inst_1) E
                      (@Semifield.toCommSemiring F (@Field.toSemifield F inst))
                      (@CommRing.toRing (@UpperTheory.Reformulated.B.Uc13.Af F inst inst_1)
                        (@IsDedekindDomain.instCommRingFiniteAdeleRing (@NumberField.RingOfIntegers F inst)
                          (@NumberField.instCommRingRingOfIntegers F inst)
                          (@NumberField.RingOfIntegers.instIsDedekindDomain F inst inst_1) F inst
                          (@NumberField.RingOfIntegers.instAlgebra_1 F inst)
                          (@NumberField.RingOfIntegers.instIsFractionRing F inst inst_1)))
                      (@IsDedekindDomain.FiniteAdeleRing.instAlgebra (@NumberField.RingOfIntegers F inst)
                        (@NumberField.instCommRingRingOfIntegers F inst)
                        (@NumberField.RingOfIntegers.instIsDedekindDomain F inst inst_1) F inst
                        (@NumberField.RingOfIntegers.instAlgebra_1 F inst)
                        (@NumberField.RingOfIntegers.instIsFractionRing F inst inst_1))
                      (@DivisionSemiring.toSemiring E (@Semifield.toDivisionSemiring E (@Field.toSemifield E inst_2)))
                      inst_4)))))
            (@UpperTheory.Reformulated.B.Uc13.intA F E inst inst_1 inst_2 inst_4)
            (@HMul.hMul
              (@TensorProduct F (@Semifield.toCommSemiring F (@Field.toSemifield F inst))
                (@UpperTheory.Reformulated.B.Uc13.Af F inst inst_1) E
                (@Semiring.toAddCommMonoid (@UpperTheory.Reformulated.B.Uc13.Af F inst inst_1)
                  (@CommSemiring.toSemiring (@UpperTheory.Reformulated.B.Uc13.Af F inst inst_1)
                    (@CommRing.toCommSemiring (@UpperTheory.Reformulated.B.Uc13.Af F inst inst_1)
                      (@IsDedekindDomain.instCommRingFiniteAdeleRing (@NumberField.RingOfIntegers F inst)
                        (@NumberField.instCommRingRingOfIntegers F inst)
                        (@NumberField.RingOfIntegers.instIsDedekindDomain F inst inst_1) F inst
                        (@NumberField.RingOfIntegers.instAlgebra_1 F inst)
                        (@NumberField.RingOfIntegers.instIsFractionRing F inst inst_1)))))
                (@Semiring.toAddCommMonoid E
                  (@DivisionSemiring.toSemiring E (@Semifield.toDivisionSemiring E (@Field.toSemifield E inst_2))))
                (@Algebra.toModule F (@UpperTheory.Reformulated.B.Uc13.Af F inst inst_1)
                  (@Semifield.toCommSemiring F (@Field.toSemifield F inst))
                  (@CommSemiring.toSemiring (@UpperTheory.Reformulated.B.Uc13.Af F inst inst_1)
                    (@CommRing.toCommSemiring (@UpperTheory.Reformulated.B.Uc13.Af F inst inst_1)
                      (@IsDedekindDomain.instCommRingFiniteAdeleRing (@NumberField.RingOfIntegers F inst)
                        (@NumberField.instCommRingRingOfIntegers F inst)
                        (@NumberField.RingOfIntegers.instIsDedekindDomain F inst inst_1) F inst
                        (@NumberField.RingOfIntegers.instAlgebra_1 F inst)
                        (@NumberField.RingOfIntegers.instIsFractionRing F inst inst_1))))
                  (@IsDedekindDomain.FiniteAdeleRing.instAlgebra (@NumberField.RingOfIntegers F inst)
                    (@NumberField.instCommRingRingOfIntegers F inst)
                    (@NumberField.RingOfIntegers.instIsDedekindDomain F inst inst_1) F inst
                    (@NumberField.RingOfIntegers.instAlgebra_1 F inst)
                    (@NumberField.RingOfIntegers.instIsFractionRing F inst inst_1)))
                (@Algebra.toModule F E (@Semifield.toCommSemiring F (@Field.toSemifield F inst))
                  (@DivisionSemiring.toSemiring E (@Semifield.toDivisionSemiring E (@Field.toSemifield E inst_2))) inst_4))
              (@TensorProduct F (@Semifield.toCommSemiring F (@Field.toSemifield F inst))
                (@UpperTheory.Reformulated.B.Uc13.Af F inst inst_1) E
                (@Semiring.toAddCommMonoid (@UpperTheory.Reformulated.B.Uc13.Af F inst inst_1)
                  (@CommSemiring.toSemiring (@UpperTheory.Reformulated.B.Uc13.Af F inst inst_1)
                    (@CommRing.toCommSemiring (@UpperTheory.Reformulated.B.Uc13.Af F inst inst_1)
                      (@IsDedekindDomain.instCommRingFiniteAdeleRing (@NumberField.RingOfIntegers F inst)
                        (@NumberField.instCommRingRingOfIntegers F inst)
                        (@NumberField.RingOfIntegers.instIsDedekindDomain F inst inst_1) F inst
                        (@NumberField.RingOfIntegers.instAlgebra_1 F inst)
                        (@NumberField.RingOfIntegers.instIsFractionRing F inst inst_1)))))
                (@Semiring.toAddCommMonoid E
                  (@DivisionSemiring.toSemiring E (@Semifield.toDivisionSemiring E (@Field.toSemifield E inst_2))))
                (@Algebra.toModule F (@UpperTheory.Reformulated.B.Uc13.Af F inst inst_1)
                  (@Semifield.toCommSemiring F (@Field.toSemifield F inst))
                  (@CommSemiring.toSemiring (@UpperTheory.Reformulated.B.Uc13.Af F inst inst_1)
                    (@CommRing.toCommSemiring (@UpperTheory.Reformulated.B.Uc13.Af F inst inst_1)
                      (@IsDedekindDomain.instCommRingFiniteAdeleRing (@NumberField.RingOfIntegers F inst)
                        (@NumberField.instCommRingRingOfIntegers F inst)
                        (@NumberField.RingOfIntegers.instIsDedekindDomain F inst inst_1) F inst
                        (@NumberField.RingOfIntegers.instAlgebra_1 F inst)
                        (@NumberField.RingOfIntegers.instIsFractionRing F inst inst_1))))
                  (@IsDedekindDomain.FiniteAdeleRing.instAlgebra (@NumberField.RingOfIntegers F inst)
                    (@NumberField.instCommRingRingOfIntegers F inst)
                    (@NumberField.RingOfIntegers.instIsDedekindDomain F inst inst_1) F inst
                    (@NumberField.RingOfIntegers.instAlgebra_1 F inst)
                    (@NumberField.RingOfIntegers.instIsFractionRing F inst inst_1)))
                (@Algebra.toModule F E (@Semifield.toCommSemiring F (@Field.toSemifield F inst))
                  (@DivisionSemiring.toSemiring E (@Semifield.toDivisionSemiring E (@Field.toSemifield E inst_2))) inst_4))
              (@TensorProduct F (@Semifield.toCommSemiring F (@Field.toSemifield F inst))
                (@UpperTheory.Reformulated.B.Uc13.Af F inst inst_1) E
                (@Semiring.toAddCommMonoid (@UpperTheory.Reformulated.B.Uc13.Af F inst inst_1)
                  (@CommSemiring.toSemiring (@UpperTheory.Reformulated.B.Uc13.Af F inst inst_1)
                    (@CommRing.toCommSemiring (@UpperTheory.Reformulated.B.Uc13.Af F inst inst_1)
                      (@IsDedekindDomain.instCommRingFiniteAdeleRing (@NumberField.RingOfIntegers F inst)
                        (@NumberField.instCommRingRingOfIntegers F inst)
                        (@NumberField.RingOfIntegers.instIsDedekindDomain F inst inst_1) F inst
                        (@NumberField.RingOfIntegers.instAlgebra_1 F inst)
                        (@NumberField.RingOfIntegers.instIsFractionRing F inst inst_1)))))
                (@Semiring.toAddCommMonoid E
                  (@DivisionSemiring.toSemiring E (@Semifield.toDivisionSemiring E (@Field.toSemifield E inst_2))))
                (@Algebra.toModule F (@UpperTheory.Reformulated.B.Uc13.Af F inst inst_1)
                  (@Semifield.toCommSemiring F (@Field.toSemifield F inst))
                  (@CommSemiring.toSemiring (@UpperTheory.Reformulated.B.Uc13.Af F inst inst_1)
                    (@CommRing.toCommSemiring (@UpperTheory.Reformulated.B.Uc13.Af F inst inst_1)
                      (@IsDedekindDomain.instCommRingFiniteAdeleRing (@NumberField.RingOfIntegers F inst)
                        (@NumberField.instCommRingRingOfIntegers F inst)
                        (@NumberField.RingOfIntegers.instIsDedekindDomain F inst inst_1) F inst
                        (@NumberField.RingOfIntegers.instAlgebra_1 F inst)
                        (@NumberField.RingOfIntegers.instIsFractionRing F inst inst_1))))
                  (@IsDedekindDomain.FiniteAdeleRing.instAlgebra (@NumberField.RingOfIntegers F inst)
                    (@NumberField.instCommRingRingOfIntegers F inst)
                    (@NumberField.RingOfIntegers.instIsDedekindDomain F inst inst_1) F inst
                    (@NumberField.RingOfIntegers.instAlgebra_1 F inst)
                    (@NumberField.RingOfIntegers.instIsFractionRing F inst inst_1)))
                (@Algebra.toModule F E (@Semifield.toCommSemiring F (@Field.toSemifield F inst))
                  (@DivisionSemiring.toSemiring E (@Semifield.toDivisionSemiring E (@Field.toSemifield E inst_2))) inst_4))
              (@instHMul
                (@TensorProduct F (@Semifield.toCommSemiring F (@Field.toSemifield F inst))
                  (@UpperTheory.Reformulated.B.Uc13.Af F inst inst_1) E
                  (@Semiring.toAddCommMonoid (@UpperTheory.Reformulated.B.Uc13.Af F inst inst_1)
                    (@CommSemiring.toSemiring (@UpperTheory.Reformulated.B.Uc13.Af F inst inst_1)
                      (@CommRing.toCommSemiring (@UpperTheory.Reformulated.B.Uc13.Af F inst inst_1)
                        (@IsDedekindDomain.instCommRingFiniteAdeleRing (@NumberField.RingOfIntegers F inst)
                          (@NumberField.instCommRingRingOfIntegers F inst)
                          (@NumberField.RingOfIntegers.instIsDedekindDomain F inst inst_1) F inst
                          (@NumberField.RingOfIntegers.instAlgebra_1 F inst)
                          (@NumberField.RingOfIntegers.instIsFractionRing F inst inst_1)))))
                  (@Semiring.toAddCommMonoid E
                    (@DivisionSemiring.toSemiring E (@Semifield.toDivisionSemiring E (@Field.toSemifield E inst_2))))
                  (@Algebra.toModule F (@UpperTheory.Reformulated.B.Uc13.Af F inst inst_1)
                    (@Semifield.toCommSemiring F (@Field.toSemifield F inst))
                    (@CommSemiring.toSemiring (@UpperTheory.Reformulated.B.Uc13.Af F inst inst_1)
                      (@CommRing.toCommSemiring (@UpperTheory.Reformulated.B.Uc13.Af F inst inst_1)
                        (@IsDedekindDomain.instCommRingFiniteAdeleRing (@NumberField.RingOfIntegers F inst)
                          (@NumberField.instCommRingRingOfIntegers F inst)
                          (@NumberField.RingOfIntegers.instIsDedekindDomain F inst inst_1) F inst
                          (@NumberField.RingOfIntegers.instAlgebra_1 F inst)
                          (@NumberField.RingOfIntegers.instIsFractionRing F inst inst_1))))
                    (@IsDedekindDomain.FiniteAdeleRing.instAlgebra (@NumberField.RingOfIntegers F inst)
                      (@NumberField.instCommRingRingOfIntegers F inst)
                      (@NumberField.RingOfIntegers.instIsDedekindDomain F inst inst_1) F inst
                      (@NumberField.RingOfIntegers.instAlgebra_1 F inst)
                      (@NumberField.RingOfIntegers.instIsFractionRing F inst inst_1)))
                  (@Algebra.toModule F E (@Semifield.toCommSemiring F (@Field.toSemifield F inst))
                    (@DivisionSemiring.toSemiring E (@Semifield.toDivisionSemiring E (@Field.toSemifield E inst_2)))
                    inst_4))
                (@Algebra.TensorProduct.instMul F (@UpperTheory.Reformulated.B.Uc13.Af F inst inst_1) E
                  (@Semifield.toCommSemiring F (@Field.toSemifield F inst))
                  (@NonUnitalNonAssocRing.toNonUnitalNonAssocSemiring (@UpperTheory.Reformulated.B.Uc13.Af F inst inst_1)
                    (@NonUnitalNonAssocCommRing.toNonUnitalNonAssocRing (@UpperTheory.Reformulated.B.Uc13.Af F inst inst_1)
                      (@NonUnitalCommRing.toNonUnitalNonAssocCommRing (@UpperTheory.Reformulated.B.Uc13.Af F inst inst_1)
                        (@CommRing.toNonUnitalCommRing (@UpperTheory.Reformulated.B.Uc13.Af F inst inst_1)
                          (@IsDedekindDomain.instCommRingFiniteAdeleRing (@NumberField.RingOfIntegers F inst)
                            (@NumberField.instCommRingRingOfIntegers F inst)
                            (@NumberField.RingOfIntegers.instIsDedekindDomain F inst inst_1) F inst
                            (@NumberField.RingOfIntegers.instAlgebra_1 F inst)
                            (@NumberField.RingOfIntegers.instIsFractionRing F inst inst_1))))))
                  (@Algebra.toModule F (@UpperTheory.Reformulated.B.Uc13.Af F inst inst_1)
                    (@Semifield.toCommSemiring F (@Field.toSemifield F inst))
                    (@CommSemiring.toSemiring (@UpperTheory.Reformulated.B.Uc13.Af F inst inst_1)
                      (@CommRing.toCommSemiring (@UpperTheory.Reformulated.B.Uc13.Af F inst inst_1)
                        (@IsDedekindDomain.instCommRingFiniteAdeleRing (@NumberField.RingOfIntegers F inst)
                          (@NumberField.instCommRingRingOfIntegers F inst)
                          (@NumberField.RingOfIntegers.instIsDedekindDomain F inst inst_1) F inst
                          (@NumberField.RingOfIntegers.instAlgebra_1 F inst)
                          (@NumberField.RingOfIntegers.instIsFractionRing F inst inst_1))))
                    (@IsDedekindDomain.FiniteAdeleRing.instAlgebra (@NumberField.RingOfIntegers F inst)
                      (@NumberField.instCommRingRingOfIntegers F inst)
                      (@NumberField.RingOfIntegers.instIsDedekindDomain F inst inst_1) F inst
                      (@NumberField.RingOfIntegers.instAlgebra_1 F inst)
                      (@NumberField.RingOfIntegers.instIsFractionRing F inst inst_1)))
                  (@Algebra.to_smulCommClass F (@UpperTheory.Reformulated.B.Uc13.Af F inst inst_1)
                    (@Semifield.toCommSemiring F (@Field.toSemifield F inst))
                    (@CommSemiring.toSemiring
                      (@IsDedekindDomain.FiniteAdeleRing (@NumberField.RingOfIntegers F inst)
                        (@NumberField.instCommRingRingOfIntegers F inst)
                        (@NumberField.RingOfIntegers.instIsDedekindDomain F inst inst_1) F inst
                        (@NumberField.RingOfIntegers.instAlgebra_1 F inst)
                        (@NumberField.RingOfIntegers.instIsFractionRing F inst inst_1))
                      (@CommRing.toCommSemiring
                        (@IsDedekindDomain.FiniteAdeleRing (@NumberField.RingOfIntegers F inst)
                          (@NumberField.instCommRingRingOfIntegers F inst)
                          (@NumberField.RingOfIntegers.instIsDedekindDomain F inst inst_1) F inst
                          (@NumberField.RingOfIntegers.instAlgebra_1 F inst)
                          (@NumberField.RingOfIntegers.instIsFractionRing F inst inst_1))
                        (@IsDedekindDomain.instCommRingFiniteAdeleRing (@NumberField.RingOfIntegers F inst)
                          (@NumberField.instCommRingRingOfIntegers F inst)
                          (@NumberField.RingOfIntegers.instIsDedekindDomain F inst inst_1) F inst
                          (@NumberField.RingOfIntegers.instAlgebra_1 F inst)
                          (@NumberField.RingOfIntegers.instIsFractionRing F inst inst_1))))
                    (@IsDedekindDomain.FiniteAdeleRing.instAlgebra (@NumberField.RingOfIntegers F inst)
                      (@NumberField.instCommRingRingOfIntegers F inst)
                      (@NumberField.RingOfIntegers.instIsDedekindDomain F inst inst_1) F inst
                      (@NumberField.RingOfIntegers.instAlgebra_1 F inst)
                      (@NumberField.RingOfIntegers.instIsFractionRing F inst inst_1)))
                  (@IsScalarTower.right F (@UpperTheory.Reformulated.B.Uc13.Af F inst inst_1)
                    (@Semifield.toCommSemiring F (@Field.toSemifield F inst))
                    (@CommSemiring.toSemiring
                      (@IsDedekindDomain.FiniteAdeleRing (@NumberField.RingOfIntegers F inst)
                        (@NumberField.instCommRingRingOfIntegers F inst)
                        (@NumberField.RingOfIntegers.instIsDedekindDomain F inst inst_1) F inst
                        (@NumberField.RingOfIntegers.instAlgebra_1 F inst)
                        (@NumberField.RingOfIntegers.instIsFractionRing F inst inst_1))
                      (@CommRing.toCommSemiring
                        (@IsDedekindDomain.FiniteAdeleRing (@NumberField.RingOfIntegers F inst)
                          (@NumberField.instCommRingRingOfIntegers F inst)
                          (@NumberField.RingOfIntegers.instIsDedekindDomain F inst inst_1) F inst
                          (@NumberField.RingOfIntegers.instAlgebra_1 F inst)
                          (@NumberField.RingOfIntegers.instIsFractionRing F inst inst_1))
                        (@IsDedekindDomain.instCommRingFiniteAdeleRing (@NumberField.RingOfIntegers F inst)
                          (@NumberField.instCommRingRingOfIntegers F inst)
                          (@NumberField.RingOfIntegers.instIsDedekindDomain F inst inst_1) F inst
                          (@NumberField.RingOfIntegers.instAlgebra_1 F inst)
                          (@NumberField.RingOfIntegers.instIsFractionRing F inst inst_1))))
                    (@IsDedekindDomain.FiniteAdeleRing.instAlgebra (@NumberField.RingOfIntegers F inst)
                      (@NumberField.instCommRingRingOfIntegers F inst)
                      (@NumberField.RingOfIntegers.instIsDedekindDomain F inst inst_1) F inst
                      (@NumberField.RingOfIntegers.instAlgebra_1 F inst)
                      (@NumberField.RingOfIntegers.instIsFractionRing F inst inst_1)))
                  (@NonUnitalNonAssocRing.toNonUnitalNonAssocSemiring E
                    (@NonUnitalNonAssocCommRing.toNonUnitalNonAssocRing E
                      (@NonUnitalCommRing.toNonUnitalNonAssocCommRing E
                        (@CommRing.toNonUnitalCommRing E (@Field.toCommRing E inst_2)))))
                  (@Algebra.toModule F E (@Semifield.toCommSemiring F (@Field.toSemifield F inst))
                    (@DivisionSemiring.toSemiring E (@Semifield.toDivisionSemiring E (@Field.toSemifield E inst_2))) inst_4)
                  (@Algebra.to_smulCommClass F E (@Semifield.toCommSemiring F (@Field.toSemifield F inst))
                    (@DivisionSemiring.toSemiring E (@Semifield.toDivisionSemiring E (@Field.toSemifield E inst_2))) inst_4)
                  (@IsScalarTower.right F E (@Semifield.toCommSemiring F (@Field.toSemifield F inst))
                    (@DivisionSemiring.toSemiring E (@Semifield.toDivisionSemiring E (@Field.toSemifield E inst_2)))
                    inst_4)))
              x y) := by sorry
