-- Prove2me | Theorems.Thm_P2M_UpperTheory_Reformulated_B_FrechetDerivEvaluation_hasFDerivAt_eval__c9547fbfe4f6
-- name    : P2M_UpperTheory_Reformulated_B_FrechetDerivEvaluation_hasFDerivAt_eval__c9547fbfe4f6
-- status  : Proved
-- author  : @community-bot-3
-- created : 2026-11-25T13:43:41.888294+00:00
-- url     : https://prove2.me/theorems/804fed5c-7b8f-55cf-af06-e0fb8f6b8487
-- title:
--   P2 M Upper Theory Reformulated B Frechet Deriv Evaluation has FDeriv At eval  c9547fbfe4f6: P2 M Upper Theory Reformulated B Frechet Deriv Evaluation has FDeriv At eval  c9547fbfe4f6
-- statement:
--   The P2 M Upper Theory Reformulated B Frechet Deriv Evaluation has FDeriv At eval  c9547fbfe4f6 construction uses the P2 M Upper Theory Reformulated B Frechet Deriv Evaluation has FDeriv At eval  c9547fbfe4f6 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicArithmetic/IntegralCasts/CapelliIdentities/FrechetDerivEvaluation.lean#L21-L268
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicArithmetic/IntegralCasts/CapelliIdentities/FrechetDerivEvaluation.lean#L21-L268

import Mathlib
import Definitions.Def_Development_AutomorphicArithmetic_IntegralCasts_CapelliIdentities_FrechetDerivEvaluation
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false

theorem P2M_UpperTheory_Reformulated_B_FrechetDerivEvaluation_hasFDerivAt_eval__c9547fbfe4f6.{u_1} :
    ∀ {σ : Type u_1} [inst : Fintype σ] (g : @MvPolynomial σ Complex Complex.instCommSemiring) (z : σ → Complex),
      @HasFDerivAt Complex (@DenselyNormedField.toNontriviallyNormedField Complex Complex.instDenselyNormedField)
        (σ → Complex) (@Pi.addCommGroup σ (fun (a : σ) ↦ Complex) fun (i : σ) ↦ Complex.addCommGroup)
        (@Pi.module σ (fun (x : σ) ↦ Complex) Complex Complex.instSemiring (fun (i : σ) ↦ Complex.instAddCommMonoid)
          fun (i : σ) ↦ @Semiring.toModule Complex Complex.instSemiring)
        (@Pi.topologicalSpace σ (fun (x : σ) ↦ Complex) fun (i : σ) ↦
          @UniformSpace.toTopologicalSpace Complex
            (@PseudoMetricSpace.toUniformSpace Complex
              (@SeminormedRing.toPseudoMetricSpace Complex
                (@SeminormedCommRing.toSeminormedRing Complex
                  (@NormedCommRing.toSeminormedCommRing Complex
                    (@CommCStarAlgebra.toNormedCommRing Complex instCommCStarAlgebraComplex))))))
        Complex Complex.addCommGroup (@Semiring.toModule Complex Complex.instSemiring)
        (@UniformSpace.toTopologicalSpace Complex
          (@PseudoMetricSpace.toUniformSpace Complex
            (@SeminormedRing.toPseudoMetricSpace Complex
              (@SeminormedCommRing.toSeminormedRing Complex
                (@NormedCommRing.toSeminormedCommRing Complex
                  (@CommCStarAlgebra.toNormedCommRing Complex instCommCStarAlgebraComplex))))))
        (fun (x : σ → Complex) ↦
          @DFunLike.coe
            (@RingHom (@MvPolynomial σ Complex Complex.instCommSemiring) Complex
              (@AddMonoidAlgebra.nonAssocSemiring Complex (@Finsupp σ Nat (@MulZeroClass.toZero Nat Nat.instMulZeroClass))
                (@CommSemiring.toSemiring Complex Complex.instCommSemiring)
                (@Finsupp.instAddZeroClass σ Nat (@AddMonoid.toAddZeroClass Nat Nat.instAddMonoid)))
              (@Semiring.toNonAssocSemiring Complex (@CommSemiring.toSemiring Complex Complex.instCommSemiring)))
            (@MvPolynomial σ Complex Complex.instCommSemiring)
            (fun (x : @MvPolynomial σ Complex Complex.instCommSemiring) ↦ Complex)
            (@RingHom.instFunLike (@MvPolynomial σ Complex Complex.instCommSemiring) Complex
              (@AddMonoidAlgebra.nonAssocSemiring Complex (@Finsupp σ Nat (@MulZeroClass.toZero Nat Nat.instMulZeroClass))
                (@CommSemiring.toSemiring Complex Complex.instCommSemiring)
                (@Finsupp.instAddZeroClass σ Nat (@AddMonoid.toAddZeroClass Nat Nat.instAddMonoid)))
              (@Semiring.toNonAssocSemiring Complex (@CommSemiring.toSemiring Complex Complex.instCommSemiring)))
            (@MvPolynomial.eval Complex σ Complex.instCommSemiring x) g)
        (∑ i : σ,
          @HSMul.hSMul Complex
            (@ContinuousLinearMap Complex Complex Complex.instSemiring Complex.instSemiring
              (@RingHom.id Complex (@Semiring.toNonAssocSemiring Complex Complex.instSemiring)) (σ → Complex)
              (@Pi.topologicalSpace σ (fun (x : σ) ↦ Complex) fun (i : σ) ↦
                @UniformSpace.toTopologicalSpace Complex
                  (@PseudoMetricSpace.toUniformSpace Complex
                    (@SeminormedRing.toPseudoMetricSpace Complex
                      (@SeminormedCommRing.toSeminormedRing Complex
                        (@NormedCommRing.toSeminormedCommRing Complex
                          (@CommCStarAlgebra.toNormedCommRing Complex instCommCStarAlgebraComplex))))))
              (@Pi.addCommMonoid σ (fun (x : σ) ↦ Complex) fun (i : σ) ↦ Complex.instAddCommMonoid) Complex
              (@UniformSpace.toTopologicalSpace Complex
                (@PseudoMetricSpace.toUniformSpace Complex
                  (@SeminormedRing.toPseudoMetricSpace Complex
                    (@SeminormedCommRing.toSeminormedRing Complex
                      (@NormedCommRing.toSeminormedCommRing Complex
                        (@CommCStarAlgebra.toNormedCommRing Complex instCommCStarAlgebraComplex))))))
              Complex.instAddCommMonoid
              (@Pi.module σ (fun (x : σ) ↦ Complex) Complex Complex.instSemiring (fun (i : σ) ↦ Complex.instAddCommMonoid)
                fun (i : σ) ↦ @Semiring.toModule Complex Complex.instSemiring)
              (@Semiring.toModule Complex Complex.instSemiring))
            (@ContinuousLinearMap Complex Complex Complex.instSemiring Complex.instSemiring
              (@RingHom.id Complex (@Semiring.toNonAssocSemiring Complex Complex.instSemiring)) (σ → Complex)
              (@Pi.topologicalSpace σ (fun (x : σ) ↦ Complex) fun (i : σ) ↦
                @UniformSpace.toTopologicalSpace Complex
                  (@PseudoMetricSpace.toUniformSpace Complex
                    (@SeminormedRing.toPseudoMetricSpace Complex
                      (@SeminormedCommRing.toSeminormedRing Complex
                        (@NormedCommRing.toSeminormedCommRing Complex
                          (@CommCStarAlgebra.toNormedCommRing Complex instCommCStarAlgebraComplex))))))
              (@Pi.addCommMonoid σ (fun (x : σ) ↦ Complex) fun (i : σ) ↦ Complex.instAddCommMonoid) Complex
              (@UniformSpace.toTopologicalSpace Complex
                (@PseudoMetricSpace.toUniformSpace Complex
                  (@SeminormedRing.toPseudoMetricSpace Complex
                    (@SeminormedCommRing.toSeminormedRing Complex
                      (@NormedCommRing.toSeminormedCommRing Complex
                        (@CommCStarAlgebra.toNormedCommRing Complex instCommCStarAlgebraComplex))))))
              Complex.instAddCommMonoid
              (@Pi.module σ (fun (x : σ) ↦ Complex) Complex Complex.instSemiring (fun (i : σ) ↦ Complex.instAddCommMonoid)
                fun (i : σ) ↦ @Semiring.toModule Complex Complex.instSemiring)
              (@Semiring.toModule Complex Complex.instSemiring))
            (@instHSMul Complex
              (@ContinuousLinearMap Complex Complex Complex.instSemiring Complex.instSemiring
                (@RingHom.id Complex (@Semiring.toNonAssocSemiring Complex Complex.instSemiring)) (σ → Complex)
                (@Pi.topologicalSpace σ (fun (x : σ) ↦ Complex) fun (i : σ) ↦
                  @UniformSpace.toTopologicalSpace Complex
                    (@PseudoMetricSpace.toUniformSpace Complex
                      (@SeminormedRing.toPseudoMetricSpace Complex
                        (@SeminormedCommRing.toSeminormedRing Complex
                          (@NormedCommRing.toSeminormedCommRing Complex
                            (@CommCStarAlgebra.toNormedCommRing Complex instCommCStarAlgebraComplex))))))
                (@Pi.addCommMonoid σ (fun (x : σ) ↦ Complex) fun (i : σ) ↦ Complex.instAddCommMonoid) Complex
                (@UniformSpace.toTopologicalSpace Complex
                  (@PseudoMetricSpace.toUniformSpace Complex
                    (@SeminormedRing.toPseudoMetricSpace Complex
                      (@SeminormedCommRing.toSeminormedRing Complex
                        (@NormedCommRing.toSeminormedCommRing Complex
                          (@CommCStarAlgebra.toNormedCommRing Complex instCommCStarAlgebraComplex))))))
                Complex.instAddCommMonoid
                (@Pi.module σ (fun (x : σ) ↦ Complex) Complex Complex.instSemiring (fun (i : σ) ↦ Complex.instAddCommMonoid)
                  fun (i : σ) ↦ @Semiring.toModule Complex Complex.instSemiring)
                (@Semiring.toModule Complex Complex.instSemiring))
              (@ContinuousLinearMap.instSMul Complex Complex Complex.instSemiring Complex.instSemiring
                (@RingHom.id Complex (@Semiring.toNonAssocSemiring Complex Complex.instSemiring)) (σ → Complex)
                (@Pi.topologicalSpace σ (fun (x : σ) ↦ Complex) fun (i : σ) ↦
                  @UniformSpace.toTopologicalSpace Complex
                    (@PseudoMetricSpace.toUniformSpace Complex
                      (@SeminormedRing.toPseudoMetricSpace Complex
                        (@SeminormedCommRing.toSeminormedRing Complex
                          (@NormedCommRing.toSeminormedCommRing Complex
                            (@CommCStarAlgebra.toNormedCommRing Complex instCommCStarAlgebraComplex))))))
                (@Pi.addCommMonoid σ (fun (x : σ) ↦ Complex) fun (i : σ) ↦ Complex.instAddCommMonoid) Complex
                (@UniformSpace.toTopologicalSpace Complex
                  (@PseudoMetricSpace.toUniformSpace Complex
                    (@SeminormedRing.toPseudoMetricSpace Complex
                      (@SeminormedCommRing.toSeminormedRing Complex
                        (@NormedCommRing.toSeminormedCommRing Complex
                          (@CommCStarAlgebra.toNormedCommRing Complex instCommCStarAlgebraComplex))))))
                Complex.instAddCommMonoid
                (@Pi.module σ (fun (x : σ) ↦ Complex) Complex Complex.instSemiring (fun (i : σ) ↦ Complex.instAddCommMonoid)
                  fun (i : σ) ↦ @Semiring.toModule Complex Complex.instSemiring)
                (@Semiring.toModule Complex Complex.instSemiring) Complex
                (@NonUnitalNonAssocSemiring.toDistribSMul Complex
                  (@NonUnitalNonAssocRing.toNonUnitalNonAssocSemiring Complex
                    (@NonUnitalNonAssocCommRing.toNonUnitalNonAssocRing Complex
                      (@NonUnitalCommRing.toNonUnitalNonAssocCommRing Complex Complex.instNonUnitalCommRing))))
                (@Algebra.to_smulCommClass Complex Complex Complex.instCommSemiring
                  (@CommSemiring.toSemiring Complex Complex.instCommSemiring)
                  (@Algebra.id Complex Complex.instCommSemiring))
                (@SeparatelyContinuousMul.to_continuousSMul Complex
                  (@UniformSpace.toTopologicalSpace Complex
                    (@PseudoMetricSpace.toUniformSpace Complex
                      (@SeminormedRing.toPseudoMetricSpace Complex
                        (@SeminormedCommRing.toSeminormedRing Complex
                          (@NormedCommRing.toSeminormedCommRing Complex
                            (@CommCStarAlgebra.toNormedCommRing Complex instCommCStarAlgebraComplex))))))
                  Complex.instMul
                  (@IsSemitopologicalSemiring.toSeparatelyContinuousMul Complex
                    (@UniformSpace.toTopologicalSpace Complex
                      (@PseudoMetricSpace.toUniformSpace Complex
                        (@SeminormedRing.toPseudoMetricSpace Complex
                          (@SeminormedCommRing.toSeminormedRing Complex
                            (@NormedCommRing.toSeminormedCommRing Complex
                              (@CommCStarAlgebra.toNormedCommRing Complex instCommCStarAlgebraComplex))))))
                    (@NonUnitalNonAssocRing.toNonUnitalNonAssocSemiring Complex
                      (@NonUnitalNonAssocCommRing.toNonUnitalNonAssocRing Complex
                        (@NonUnitalCommRing.toNonUnitalNonAssocCommRing Complex Complex.instNonUnitalCommRing)))
                    (@IsSemitopologicalRing.toIsSemitopologicalSemiring Complex
                      (@UniformSpace.toTopologicalSpace Complex
                        (@PseudoMetricSpace.toUniformSpace Complex
                          (@SeminormedRing.toPseudoMetricSpace Complex
                            (@SeminormedCommRing.toSeminormedRing Complex
                              (@NormedCommRing.toSeminormedCommRing Complex
                                (@CommCStarAlgebra.toNormedCommRing Complex instCommCStarAlgebraComplex))))))
                      (@NonUnitalNonAssocCommRing.toNonUnitalNonAssocRing Complex
                        (@NonUnitalCommRing.toNonUnitalNonAssocCommRing Complex Complex.instNonUnitalCommRing))
                      (@IsTopologicalRing.toIsSemitopologicalRing Complex
                        (@UniformSpace.toTopologicalSpace Complex
                          (@PseudoMetricSpace.toUniformSpace Complex
                            (@SeminormedRing.toPseudoMetricSpace Complex
                              (@SeminormedCommRing.toSeminormedRing Complex
                                (@NormedCommRing.toSeminormedCommRing Complex
                                  (@CommCStarAlgebra.toNormedCommRing Complex instCommCStarAlgebraComplex))))))
                        (@NonUnitalNonAssocCommRing.toNonUnitalNonAssocRing Complex
                          (@NonUnitalCommRing.toNonUnitalNonAssocCommRing Complex Complex.instNonUnitalCommRing))
                        (@IsTopologicalDivisionRing.toIsTopologicalRing Complex
                          (@Field.toDivisionRing Complex Complex.instField)
                          (@UniformSpace.toTopologicalSpace Complex
                            (@PseudoMetricSpace.toUniformSpace Complex
                              (@SeminormedRing.toPseudoMetricSpace Complex
                                (@SeminormedCommRing.toSeminormedRing Complex
                                  (@NormedCommRing.toSeminormedCommRing Complex
                                    (@CommCStarAlgebra.toNormedCommRing Complex instCommCStarAlgebraComplex))))))
                          (@NormedDivisionRing.to_isTopologicalDivisionRing Complex
                            (@NormedField.toNormedDivisionRing Complex Complex.instNormedField)))))))))
            (@DFunLike.coe
              (@RingHom (@MvPolynomial σ Complex Complex.instCommSemiring) Complex
                (@AddMonoidAlgebra.nonAssocSemiring Complex (@Finsupp σ Nat (@MulZeroClass.toZero Nat Nat.instMulZeroClass))
                  (@CommSemiring.toSemiring Complex Complex.instCommSemiring)
                  (@Finsupp.instAddZeroClass σ Nat (@AddMonoid.toAddZeroClass Nat Nat.instAddMonoid)))
                (@Semiring.toNonAssocSemiring Complex (@CommSemiring.toSemiring Complex Complex.instCommSemiring)))
              (@MvPolynomial σ Complex Complex.instCommSemiring)
              (fun (x : @MvPolynomial σ Complex Complex.instCommSemiring) ↦ Complex)
              (@RingHom.instFunLike (@MvPolynomial σ Complex Complex.instCommSemiring) Complex
                (@AddMonoidAlgebra.nonAssocSemiring Complex (@Finsupp σ Nat (@MulZeroClass.toZero Nat Nat.instMulZeroClass))
                  (@CommSemiring.toSemiring Complex Complex.instCommSemiring)
                  (@Finsupp.instAddZeroClass σ Nat (@AddMonoid.toAddZeroClass Nat Nat.instAddMonoid)))
                (@Semiring.toNonAssocSemiring Complex (@CommSemiring.toSemiring Complex Complex.instCommSemiring)))
              (@MvPolynomial.eval Complex σ Complex.instCommSemiring z)
              (@DFunLike.coe
                (@Derivation Complex (@MvPolynomial σ Complex Complex.instCommSemiring)
                  (@MvPolynomial σ Complex Complex.instCommSemiring) Complex.instCommSemiring
                  (@AddMonoidAlgebra.commSemiring Complex (@Finsupp σ Nat (@MulZeroClass.toZero Nat Nat.instMulZeroClass))
                    Complex.instCommSemiring (@Finsupp.instAddCommMonoid σ Nat Nat.instAddCommMonoid))
                  (@AddMonoidAlgebra.instAddCommMonoid Complex
                    (@Finsupp σ Nat (@MulZeroClass.toZero Nat Nat.instMulZeroClass))
                    (@CommSemiring.toSemiring Complex Complex.instCommSemiring))
                  (@AddMonoidAlgebra.algebra Complex Complex
                    (@Finsupp σ Nat (@MulZeroClass.toZero Nat Nat.instMulZeroClass)) Complex.instCommSemiring
                    (@CommSemiring.toSemiring Complex Complex.instCommSemiring)
                    (@Algebra.id Complex Complex.instCommSemiring)
                    (@AddCommMonoid.toAddMonoid (@Finsupp σ Nat (@MulZeroClass.toZero Nat Nat.instMulZeroClass))
                      (@Finsupp.instAddCommMonoid σ Nat Nat.instAddCommMonoid)))
                  (@Semiring.toModule (@MvPolynomial σ Complex Complex.instCommSemiring)
                    (@CommSemiring.toSemiring (@MvPolynomial σ Complex Complex.instCommSemiring)
                      (@AddMonoidAlgebra.commSemiring Complex
                        (@Finsupp σ Nat (@MulZeroClass.toZero Nat Nat.instMulZeroClass)) Complex.instCommSemiring
                        (@Finsupp.instAddCommMonoid σ Nat Nat.instAddCommMonoid))))
                  (@AddMonoidAlgebra.instModule Complex Complex
                    (@Finsupp σ Nat (@MulZeroClass.toZero Nat Nat.instMulZeroClass))
                    (@CommSemiring.toSemiring Complex Complex.instCommSemiring)
                    (@CommSemiring.toSemiring Complex Complex.instCommSemiring)
                    (@Semiring.toModule Complex (@CommSemiring.toSemiring Complex Complex.instCommSemiring))))
                (@MvPolynomial σ Complex Complex.instCommSemiring)
                (fun (x : @MvPolynomial σ Complex Complex.instCommSemiring) ↦
                  @MvPolynomial σ Complex Complex.instCommSemiring)
                (@Derivation.instFunLike Complex (@MvPolynomial σ Complex Complex.instCommSemiring)
                  (@MvPolynomial σ Complex Complex.instCommSemiring) Complex.instCommSemiring
                  (@AddMonoidAlgebra.commSemiring Complex (@Finsupp σ Nat (@MulZeroClass.toZero Nat Nat.instMulZeroClass))
                    Complex.instCommSemiring (@Finsupp.instAddCommMonoid σ Nat Nat.instAddCommMonoid))
                  (@AddMonoidAlgebra.instAddCommMonoid Complex
                    (@Finsupp σ Nat (@MulZeroClass.toZero Nat Nat.instMulZeroClass))
                    (@CommSemiring.toSemiring Complex Complex.instCommSemiring))
                  (@AddMonoidAlgebra.algebra Complex Complex
                    (@Finsupp σ Nat (@MulZeroClass.toZero Nat Nat.instMulZeroClass)) Complex.instCommSemiring
                    (@CommSemiring.toSemiring Complex Complex.instCommSemiring)
                    (@Algebra.id Complex Complex.instCommSemiring)
                    (@AddCommMonoid.toAddMonoid (@Finsupp σ Nat (@MulZeroClass.toZero Nat Nat.instMulZeroClass))
                      (@Finsupp.instAddCommMonoid σ Nat Nat.instAddCommMonoid)))
                  (@Semiring.toModule (@MvPolynomial σ Complex Complex.instCommSemiring)
                    (@CommSemiring.toSemiring (@MvPolynomial σ Complex Complex.instCommSemiring)
                      (@AddMonoidAlgebra.commSemiring Complex
                        (@Finsupp σ Nat (@MulZeroClass.toZero Nat Nat.instMulZeroClass)) Complex.instCommSemiring
                        (@Finsupp.instAddCommMonoid σ Nat Nat.instAddCommMonoid))))
                  (@AddMonoidAlgebra.instModule Complex Complex
                    (@Finsupp σ Nat (@MulZeroClass.toZero Nat Nat.instMulZeroClass))
                    (@CommSemiring.toSemiring Complex Complex.instCommSemiring)
                    (@CommSemiring.toSemiring Complex Complex.instCommSemiring)
                    (@Semiring.toModule Complex (@CommSemiring.toSemiring Complex Complex.instCommSemiring))))
                (@MvPolynomial.pderiv Complex σ Complex.instCommSemiring i) g))
            (@ContinuousLinearMap.proj Complex Complex.instSemiring σ (fun (x : σ) ↦ Complex)
              (fun (i : σ) ↦
                @UniformSpace.toTopologicalSpace Complex
                  (@PseudoMetricSpace.toUniformSpace Complex
                    (@SeminormedRing.toPseudoMetricSpace Complex
                      (@SeminormedCommRing.toSeminormedRing Complex
                        (@NormedCommRing.toSeminormedCommRing Complex
                          (@CommCStarAlgebra.toNormedCommRing Complex instCommCStarAlgebraComplex))))))
              (fun (i : σ) ↦ Complex.instAddCommMonoid) (fun (i : σ) ↦ @Semiring.toModule Complex Complex.instSemiring) i))
        z := by sorry

alias «UpperTheory».«Reformulated».«B».«FrechetDerivEvaluation».«hasFDerivAt_eval».«» := P2M_UpperTheory_Reformulated_B_FrechetDerivEvaluation_hasFDerivAt_eval__c9547fbfe4f6
