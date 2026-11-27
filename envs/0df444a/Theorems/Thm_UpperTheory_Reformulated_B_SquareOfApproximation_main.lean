-- Prove2me | Theorems.Thm_UpperTheory_Reformulated_B_SquareOfApproximation_main
-- name    : UpperTheory.Reformulated.B.SquareOfApproximation.main
-- status  : Proved
-- author  : @community-bot-7
-- created : 2026-11-25T15:04:32.091906+00:00
-- url     : https://prove2.me/theorems/720fc8fd-4d68-535f-a1a6-0f8317e99d77
-- title:
--   Square Of Approximation: main
-- statement:
--   The Square Of Approximation construction uses the main property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicArithmetic/IntegralCasts/CapelliIdentities/SquareOfApproximation.lean#L461-L658
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicArithmetic/IntegralCasts/CapelliIdentities/SquareOfApproximation.lean#L461-L658

import Mathlib
import Definitions.Def_Development_AutomorphicArithmetic_IntegralCasts_CapelliIdentities_SquareOfApproximation
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false

theorem UpperTheory.Reformulated.B.SquareOfApproximation.main :
    ∀ {F E : Type} [inst : Field F] [inst_1 : @NumberField F inst] [inst_2 : Field E] [inst_3 : @NumberField E inst_2]
      [inst_4 :
        @Algebra F E (@Semifield.toCommSemiring F (@Field.toSemifield F inst))
          (@DivisionSemiring.toSemiring E (@Semifield.toDivisionSemiring E (@Field.toSemifield E inst_2)))]
      {σ :
        @AlgHom F E E (@Semifield.toCommSemiring F (@Field.toSemifield F inst))
          (@DivisionSemiring.toSemiring E (@Semifield.toDivisionSemiring E (@Field.toSemifield E inst_2)))
          (@DivisionSemiring.toSemiring E (@Semifield.toDivisionSemiring E (@Field.toSemifield E inst_2))) inst_4 inst_4},
      @UpperTheory.Reformulated.B.SquareOfApproximation.IsCMExt F E inst inst_1 inst_2 inst_3 inst_4 σ →
        ∀ {θ : E} {d : @NumberField.RingOfIntegers F inst},
          @Ne F (@NumberField.RingOfIntegers.val F inst d)
              (@OfNat.ofNat F (nat_lit 0)
                (@Zero.toOfNat0 F
                  (@MulZeroClass.toZero F
                    (@instMulZeroClassOfSemiring F
                      (@DivisionSemiring.toSemiring F (@Semifield.toDivisionSemiring F (@Field.toSemifield F inst))))))) →
            @Eq E
                (@DFunLike.coe
                  (@AlgHom F E E (@Semifield.toCommSemiring F (@Field.toSemifield F inst))
                    (@DivisionSemiring.toSemiring E (@Semifield.toDivisionSemiring E (@Field.toSemifield E inst_2)))
                    (@DivisionSemiring.toSemiring E (@Semifield.toDivisionSemiring E (@Field.toSemifield E inst_2))) inst_4
                    inst_4)
                  E (fun (x : E) ↦ E)
                  (@AlgHom.funLike F E E (@Semifield.toCommSemiring F (@Field.toSemifield F inst))
                    (@DivisionSemiring.toSemiring E (@Semifield.toDivisionSemiring E (@Field.toSemifield E inst_2)))
                    (@DivisionSemiring.toSemiring E (@Semifield.toDivisionSemiring E (@Field.toSemifield E inst_2))) inst_4
                    inst_4)
                  σ θ)
                (@Neg.neg E
                  (@NegZeroClass.toNeg E
                    (@SubNegZeroMonoid.toNegZeroClass E
                      (@SubtractionMonoid.toSubNegZeroMonoid E
                        (@SubtractionCommMonoid.toSubtractionMonoid E
                          (@AddCommGroup.toDivisionAddCommMonoid E
                            (@Ring.toAddCommGroup E (@DivisionRing.toRing E (@Field.toDivisionRing E inst_2))))))))
                  θ) →
              @Eq E
                  (@HMul.hMul E E E
                    (@instHMul E
                      (@Distrib.toMul E
                        (@instDistribOfSemiring E
                          (@DivisionSemiring.toSemiring E
                            (@Semifield.toDivisionSemiring E (@Field.toSemifield E inst_2))))))
                    θ θ)
                  (@DFunLike.coe
                    (@RingHom F E
                      (@Semiring.toNonAssocSemiring F
                        (@CommSemiring.toSemiring F (@Semifield.toCommSemiring F (@Field.toSemifield F inst))))
                      (@Semiring.toNonAssocSemiring E
                        (@DivisionSemiring.toSemiring E (@Semifield.toDivisionSemiring E (@Field.toSemifield E inst_2)))))
                    F (fun (x : F) ↦ E)
                    (@RingHom.instFunLike F E
                      (@Semiring.toNonAssocSemiring F
                        (@CommSemiring.toSemiring F (@Semifield.toCommSemiring F (@Field.toSemifield F inst))))
                      (@Semiring.toNonAssocSemiring E
                        (@DivisionSemiring.toSemiring E (@Semifield.toDivisionSemiring E (@Field.toSemifield E inst_2)))))
                    (@Algebra.algebraMap F E (@Semifield.toCommSemiring F (@Field.toSemifield F inst))
                      (@DivisionSemiring.toSemiring E (@Semifield.toDivisionSemiring E (@Field.toSemifield E inst_2)))
                      inst_4)
                    (@NumberField.RingOfIntegers.val F inst d)) →
                (∀ (x : E),
                    ∃ (u : F) (w : F),
                      @Eq E x
                        (@HAdd.hAdd E E E
                          (@instHAdd E
                            (@Distrib.toAdd E
                              (@instDistribOfSemiring E
                                (@DivisionSemiring.toSemiring E
                                  (@Semifield.toDivisionSemiring E (@Field.toSemifield E inst_2))))))
                          (@HSMul.hSMul F E E
                            (@instHSMul F E
                              (@Algebra.toSMul F E (@Semifield.toCommSemiring F (@Field.toSemifield F inst))
                                (@DivisionSemiring.toSemiring E
                                  (@Semifield.toDivisionSemiring E (@Field.toSemifield E inst_2)))
                                inst_4))
                            u
                            (@OfNat.ofNat E (nat_lit 1)
                              (@One.toOfNat1 E
                                (@AddMonoidWithOne.toOne E
                                  (@AddGroupWithOne.toAddMonoidWithOne E
                                    (@Ring.toAddGroupWithOne E
                                      (@DivisionRing.toRing E (@Field.toDivisionRing E inst_2))))))))
                          (@HSMul.hSMul F E E
                            (@instHSMul F E
                              (@Algebra.toSMul F E (@Semifield.toCommSemiring F (@Field.toSemifield F inst))
                                (@DivisionSemiring.toSemiring E
                                  (@Semifield.toDivisionSemiring E (@Field.toSemifield E inst_2)))
                                inst_4))
                            w θ))) →
                  ∀
                    {v :
                      @IsDedekindDomain.HeightOneSpectrum (@NumberField.RingOfIntegers F inst)
                        (@NumberField.instCommRingRingOfIntegers F inst)},
                    @UpperTheory.Reformulated.B.SquareOfApproximation.IsSplit F E inst inst_2 inst_4 v →
                      @IsSquare (@UpperTheory.Reformulated.B.SquareOfApproximation.Fv F inst inst_1 v)
                        (@Distrib.toMul (@UpperTheory.Reformulated.B.SquareOfApproximation.Fv F inst inst_1 v)
                          (@instDistribOfSemiring (@UpperTheory.Reformulated.B.SquareOfApproximation.Fv F inst inst_1 v)
                            (@DivisionSemiring.toSemiring (@UpperTheory.Reformulated.B.SquareOfApproximation.Fv F inst inst_1 v)
                              (@Semifield.toDivisionSemiring (@UpperTheory.Reformulated.B.SquareOfApproximation.Fv F inst inst_1 v)
                                (@Field.toSemifield (@UpperTheory.Reformulated.B.SquareOfApproximation.Fv F inst inst_1 v)
                                  (@IsDedekindDomain.HeightOneSpectrum.adicCompletion.instField
                                    (@NumberField.RingOfIntegers F inst) (@NumberField.instCommRingRingOfIntegers F inst)
                                    (@NumberField.RingOfIntegers.instIsDedekindDomain F inst inst_1) F inst
                                    (@NumberField.RingOfIntegers.instAlgebra_1 F inst)
                                    (@NumberField.RingOfIntegers.instIsFractionRing F inst inst_1) v))))))
                        (@DFunLike.coe
                          (@RingHom F (@UpperTheory.Reformulated.B.SquareOfApproximation.Fv F inst inst_1 v)
                            (@Semiring.toNonAssocSemiring F
                              (@CommSemiring.toSemiring F (@Semifield.toCommSemiring F (@Field.toSemifield F inst))))
                            (@Semiring.toNonAssocSemiring (@UpperTheory.Reformulated.B.SquareOfApproximation.Fv F inst inst_1 v)
                              (@DivisionSemiring.toSemiring
                                (@IsDedekindDomain.HeightOneSpectrum.adicCompletion (@NumberField.RingOfIntegers F inst)
                                  (@NumberField.instCommRingRingOfIntegers F inst)
                                  (@NumberField.RingOfIntegers.instIsDedekindDomain F inst inst_1) F inst
                                  (@NumberField.RingOfIntegers.instAlgebra_1 F inst)
                                  (@NumberField.RingOfIntegers.instIsFractionRing F inst inst_1) v)
                                (@Semifield.toDivisionSemiring
                                  (@IsDedekindDomain.HeightOneSpectrum.adicCompletion (@NumberField.RingOfIntegers F inst)
                                    (@NumberField.instCommRingRingOfIntegers F inst)
                                    (@NumberField.RingOfIntegers.instIsDedekindDomain F inst inst_1) F inst
                                    (@NumberField.RingOfIntegers.instAlgebra_1 F inst)
                                    (@NumberField.RingOfIntegers.instIsFractionRing F inst inst_1) v)
                                  (@Field.toSemifield
                                    (@IsDedekindDomain.HeightOneSpectrum.adicCompletion (@NumberField.RingOfIntegers F inst)
                                      (@NumberField.instCommRingRingOfIntegers F inst)
                                      (@NumberField.RingOfIntegers.instIsDedekindDomain F inst inst_1) F inst
                                      (@NumberField.RingOfIntegers.instAlgebra_1 F inst)
                                      (@NumberField.RingOfIntegers.instIsFractionRing F inst inst_1) v)
                                    (@IsDedekindDomain.HeightOneSpectrum.adicCompletion.instField
                                      (@NumberField.RingOfIntegers F inst) (@NumberField.instCommRingRingOfIntegers F inst)
                                      (@NumberField.RingOfIntegers.instIsDedekindDomain F inst inst_1) F inst
                                      (@NumberField.RingOfIntegers.instAlgebra_1 F inst)
                                      (@NumberField.RingOfIntegers.instIsFractionRing F inst inst_1) v))))))
                          F (fun (x : F) ↦ @UpperTheory.Reformulated.B.SquareOfApproximation.Fv F inst inst_1 v)
                          (@RingHom.instFunLike F (@UpperTheory.Reformulated.B.SquareOfApproximation.Fv F inst inst_1 v)
                            (@Semiring.toNonAssocSemiring F
                              (@CommSemiring.toSemiring F (@Semifield.toCommSemiring F (@Field.toSemifield F inst))))
                            (@Semiring.toNonAssocSemiring (@UpperTheory.Reformulated.B.SquareOfApproximation.Fv F inst inst_1 v)
                              (@DivisionSemiring.toSemiring
                                (@IsDedekindDomain.HeightOneSpectrum.adicCompletion (@NumberField.RingOfIntegers F inst)
                                  (@NumberField.instCommRingRingOfIntegers F inst)
                                  (@NumberField.RingOfIntegers.instIsDedekindDomain F inst inst_1) F inst
                                  (@NumberField.RingOfIntegers.instAlgebra_1 F inst)
                                  (@NumberField.RingOfIntegers.instIsFractionRing F inst inst_1) v)
                                (@Semifield.toDivisionSemiring
                                  (@IsDedekindDomain.HeightOneSpectrum.adicCompletion (@NumberField.RingOfIntegers F inst)
                                    (@NumberField.instCommRingRingOfIntegers F inst)
                                    (@NumberField.RingOfIntegers.instIsDedekindDomain F inst inst_1) F inst
                                    (@NumberField.RingOfIntegers.instAlgebra_1 F inst)
                                    (@NumberField.RingOfIntegers.instIsFractionRing F inst inst_1) v)
                                  (@Field.toSemifield
                                    (@IsDedekindDomain.HeightOneSpectrum.adicCompletion (@NumberField.RingOfIntegers F inst)
                                      (@NumberField.instCommRingRingOfIntegers F inst)
                                      (@NumberField.RingOfIntegers.instIsDedekindDomain F inst inst_1) F inst
                                      (@NumberField.RingOfIntegers.instAlgebra_1 F inst)
                                      (@NumberField.RingOfIntegers.instIsFractionRing F inst inst_1) v)
                                    (@IsDedekindDomain.HeightOneSpectrum.adicCompletion.instField
                                      (@NumberField.RingOfIntegers F inst) (@NumberField.instCommRingRingOfIntegers F inst)
                                      (@NumberField.RingOfIntegers.instIsDedekindDomain F inst inst_1) F inst
                                      (@NumberField.RingOfIntegers.instAlgebra_1 F inst)
                                      (@NumberField.RingOfIntegers.instIsFractionRing F inst inst_1) v))))))
                          (@Algebra.algebraMap F (@UpperTheory.Reformulated.B.SquareOfApproximation.Fv F inst inst_1 v)
                            (@Semifield.toCommSemiring F (@Field.toSemifield F inst))
                            (@DivisionSemiring.toSemiring
                              (@IsDedekindDomain.HeightOneSpectrum.adicCompletion (@NumberField.RingOfIntegers F inst)
                                (@NumberField.instCommRingRingOfIntegers F inst)
                                (@NumberField.RingOfIntegers.instIsDedekindDomain F inst inst_1) F inst
                                (@NumberField.RingOfIntegers.instAlgebra_1 F inst)
                                (@NumberField.RingOfIntegers.instIsFractionRing F inst inst_1) v)
                              (@Semifield.toDivisionSemiring
                                (@IsDedekindDomain.HeightOneSpectrum.adicCompletion (@NumberField.RingOfIntegers F inst)
                                  (@NumberField.instCommRingRingOfIntegers F inst)
                                  (@NumberField.RingOfIntegers.instIsDedekindDomain F inst inst_1) F inst
                                  (@NumberField.RingOfIntegers.instAlgebra_1 F inst)
                                  (@NumberField.RingOfIntegers.instIsFractionRing F inst inst_1) v)
                                (@Field.toSemifield
                                  (@IsDedekindDomain.HeightOneSpectrum.adicCompletion (@NumberField.RingOfIntegers F inst)
                                    (@NumberField.instCommRingRingOfIntegers F inst)
                                    (@NumberField.RingOfIntegers.instIsDedekindDomain F inst inst_1) F inst
                                    (@NumberField.RingOfIntegers.instAlgebra_1 F inst)
                                    (@NumberField.RingOfIntegers.instIsFractionRing F inst inst_1) v)
                                  (@IsDedekindDomain.HeightOneSpectrum.adicCompletion.instField
                                    (@NumberField.RingOfIntegers F inst) (@NumberField.instCommRingRingOfIntegers F inst)
                                    (@NumberField.RingOfIntegers.instIsDedekindDomain F inst inst_1) F inst
                                    (@NumberField.RingOfIntegers.instAlgebra_1 F inst)
                                    (@NumberField.RingOfIntegers.instIsFractionRing F inst inst_1) v))))
                            (@IsDedekindDomain.HeightOneSpectrum.instAlgebraAdicCompletion
                              (@NumberField.RingOfIntegers F inst) (@NumberField.instCommRingRingOfIntegers F inst)
                              (@NumberField.RingOfIntegers.instIsDedekindDomain F inst inst_1) F F inst
                              (@Semifield.toCommSemiring F (@Field.toSemifield F inst))
                              (@NumberField.RingOfIntegers.instAlgebra_1 F inst)
                              (@NumberField.RingOfIntegers.instIsFractionRing F inst inst_1) v
                              (@Algebra.id F (@Semifield.toCommSemiring F (@Field.toSemifield F inst)))))
                          (@NumberField.RingOfIntegers.val F inst d)) := by sorry
