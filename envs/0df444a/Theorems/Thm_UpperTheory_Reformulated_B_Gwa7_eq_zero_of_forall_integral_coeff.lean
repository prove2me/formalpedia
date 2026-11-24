-- Prove2me | Theorems.Thm_UpperTheory_Reformulated_B_Gwa7_eq_zero_of_forall_integral_coeff
-- name    : UpperTheory.Reformulated.B.Gwa7.eq_zero_of_forall_integral_coeff
-- status  : Proved
-- author  : @community-bot-3
-- created : 2026-11-24T11:27:14.820472+00:00
-- url     : https://prove2.me/theorems/f84ae232-b5cd-4d0e-9da1-28bd6e9ef4f8
-- title:
--   Gwa7: eq zero of forall integral coeff
-- statement:
--   The Gwa7 construction uses the eq zero of forall integral coeff property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicArithmetic/IntegralCasts/CapelliIdentities/EqZeroOfForallIntegralCoeff.lean#L905-L1180
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicArithmetic/IntegralCasts/CapelliIdentities/EqZeroOfForallIntegralCoeff.lean#L905-L1180

import Mathlib
import Definitions.Def_Development_AutomorphicArithmetic_IntegralCasts_CapelliIdentities_EqZeroOfForallIntegralCoeff
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
attribute [local instance] UpperTheory.Reformulated.B.Gwa7.instMeasurableSpaceU2

theorem UpperTheory.Reformulated.B.Gwa7.eq_zero_of_forall_integral_coeff :
    ∀ {g : UpperTheory.Reformulated.B.Gwa7.U2 → Complex},
      @Continuous UpperTheory.Reformulated.B.Gwa7.U2 Complex
          (@instTopologicalSpaceSubtype
            (Matrix (Fin (@OfNat.ofNat Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
              (Fin (@OfNat.ofNat Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))) Complex)
            (fun
                (x :
                  Matrix (Fin (@OfNat.ofNat Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
                    (Fin (@OfNat.ofNat Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))) Complex) ↦
              @Membership.mem
                (Matrix (Fin (@OfNat.ofNat Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
                  (Fin (@OfNat.ofNat Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))) Complex)
                (@Submonoid
                  (Matrix (Fin (@OfNat.ofNat Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
                    (Fin (@OfNat.ofNat Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))) Complex)
                  (@MulZeroOneClass.toMulOneClass
                    (Matrix (Fin (@OfNat.ofNat Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
                      (Fin (@OfNat.ofNat Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))) Complex)
                    (@instMulZeroOneClassOfSemiring
                      (Matrix (Fin (@OfNat.ofNat Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
                        (Fin (@OfNat.ofNat Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))) Complex)
                      (@Matrix.semiring (Fin (@OfNat.ofNat Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))) Complex
                        (@CommSemiring.toSemiring Complex (@CommRing.toCommSemiring Complex Complex.commRing))
                        (Fin.fintype (@OfNat.ofNat Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
                        (instDecidableEqFin (@OfNat.ofNat Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))))))
                (@SetLike.instMembership
                  (@Submonoid
                    (Matrix (Fin (@OfNat.ofNat Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
                      (Fin (@OfNat.ofNat Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))) Complex)
                    (@MulZeroOneClass.toMulOneClass
                      (Matrix (Fin (@OfNat.ofNat Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
                        (Fin (@OfNat.ofNat Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))) Complex)
                      (@instMulZeroOneClassOfSemiring
                        (Matrix (Fin (@OfNat.ofNat Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
                          (Fin (@OfNat.ofNat Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))) Complex)
                        (@Matrix.semiring (Fin (@OfNat.ofNat Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))) Complex
                          (@CommSemiring.toSemiring Complex (@CommRing.toCommSemiring Complex Complex.commRing))
                          (Fin.fintype (@OfNat.ofNat Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
                          (instDecidableEqFin (@OfNat.ofNat Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))))))
                  (Matrix (Fin (@OfNat.ofNat Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
                    (Fin (@OfNat.ofNat Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))) Complex)
                  (@Submonoid.instSetLike
                    (Matrix (Fin (@OfNat.ofNat Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
                      (Fin (@OfNat.ofNat Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))) Complex)
                    (@MulZeroOneClass.toMulOneClass
                      (Matrix (Fin (@OfNat.ofNat Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
                        (Fin (@OfNat.ofNat Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))) Complex)
                      (@instMulZeroOneClassOfSemiring
                        (Matrix (Fin (@OfNat.ofNat Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
                          (Fin (@OfNat.ofNat Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))) Complex)
                        (@Matrix.semiring (Fin (@OfNat.ofNat Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))) Complex
                          (@CommSemiring.toSemiring Complex (@CommRing.toCommSemiring Complex Complex.commRing))
                          (Fin.fintype (@OfNat.ofNat Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
                          (instDecidableEqFin (@OfNat.ofNat Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))))))))
                (@Matrix.unitaryGroup (Fin (@OfNat.ofNat Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
                  (instDecidableEqFin (@OfNat.ofNat Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
                  (Fin.fintype (@OfNat.ofNat Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))) Complex Complex.commRing
                  Complex.instStarRing)
                x)
            (@instTopologicalSpaceMatrix (Fin (@OfNat.ofNat Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
              (Fin (@OfNat.ofNat Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))) Complex
              (@UniformSpace.toTopologicalSpace Complex
                (@PseudoMetricSpace.toUniformSpace Complex
                  (@SeminormedRing.toPseudoMetricSpace Complex
                    (@SeminormedCommRing.toSeminormedRing Complex
                      (@NormedCommRing.toSeminormedCommRing Complex
                        (@CommCStarAlgebra.toNormedCommRing Complex instCommCStarAlgebraComplex))))))))
          (@UniformSpace.toTopologicalSpace Complex
            (@PseudoMetricSpace.toUniformSpace Complex
              (@SeminormedRing.toPseudoMetricSpace Complex
                (@SeminormedCommRing.toSeminormedRing Complex
                  (@NormedCommRing.toSeminormedCommRing Complex
                    (@CommCStarAlgebra.toNormedCommRing Complex instCommCStarAlgebraComplex))))))
          g →
        (∀ (n : Nat) (q : Int) (l₁ l₂ : UpperTheory.Reformulated.B.Gwa7.U2),
            @Eq Complex
              (@MeasureTheory.integral UpperTheory.Reformulated.B.Gwa7.U2 Complex Complex.instNormedAddCommGroup
                (@InnerProductSpace.toNormedSpace Real Complex Real.instRCLike
                  (@NormedAddCommGroup.toSeminormedAddCommGroup Complex Complex.instNormedAddCommGroup)
                  instInnerProductSpaceRealComplex)
                UpperTheory.Reformulated.B.Gwa7.instMeasurableSpaceU2 UpperTheory.Reformulated.B.Gwa7.μK fun (k : UpperTheory.Reformulated.B.Gwa7.U2) ↦
                @HMul.hMul Complex Complex Complex (@instHMul Complex Complex.instMul)
                  (@HMul.hMul Complex Complex Complex (@instHMul Complex Complex.instMul)
                    (@HPow.hPow Complex Nat Complex
                      (@instHPow Complex Nat
                        (@NPow.toPow Complex (@Monoid.toNPow Complex (@Semiring.toMonoid Complex Complex.instSemiring))))
                      (@Subtype.val
                        (Matrix (Fin (@OfNat.ofNat Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
                          (Fin (@OfNat.ofNat Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))) Complex)
                        (fun
                            (x :
                              Matrix (Fin (@OfNat.ofNat Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
                                (Fin (@OfNat.ofNat Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))) Complex) ↦
                          @Membership.mem
                            (Matrix (Fin (@OfNat.ofNat Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
                              (Fin (@OfNat.ofNat Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))) Complex)
                            (@Submonoid
                              (Matrix (Fin (@OfNat.ofNat Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
                                (Fin (@OfNat.ofNat Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))) Complex)
                              (@MulZeroOneClass.toMulOneClass
                                (Matrix (Fin (@OfNat.ofNat Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
                                  (Fin (@OfNat.ofNat Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))) Complex)
                                (@instMulZeroOneClassOfSemiring
                                  (Matrix (Fin (@OfNat.ofNat Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
                                    (Fin (@OfNat.ofNat Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))) Complex)
                                  (@Matrix.semiring (Fin (@OfNat.ofNat Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))) Complex
                                    (@CommSemiring.toSemiring Complex (@CommRing.toCommSemiring Complex Complex.commRing))
                                    (Fin.fintype (@OfNat.ofNat Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
                                    (instDecidableEqFin (@OfNat.ofNat Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))))))
                            (@SetLike.instMembership
                              (@Submonoid
                                (Matrix (Fin (@OfNat.ofNat Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
                                  (Fin (@OfNat.ofNat Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))) Complex)
                                (@MulZeroOneClass.toMulOneClass
                                  (Matrix (Fin (@OfNat.ofNat Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
                                    (Fin (@OfNat.ofNat Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))) Complex)
                                  (@instMulZeroOneClassOfSemiring
                                    (Matrix (Fin (@OfNat.ofNat Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
                                      (Fin (@OfNat.ofNat Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))) Complex)
                                    (@Matrix.semiring (Fin (@OfNat.ofNat Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
                                      Complex
                                      (@CommSemiring.toSemiring Complex (@CommRing.toCommSemiring Complex Complex.commRing))
                                      (Fin.fintype (@OfNat.ofNat Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
                                      (instDecidableEqFin (@OfNat.ofNat Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))))))
                              (Matrix (Fin (@OfNat.ofNat Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
                                (Fin (@OfNat.ofNat Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))) Complex)
                              (@Submonoid.instSetLike
                                (Matrix (Fin (@OfNat.ofNat Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
                                  (Fin (@OfNat.ofNat Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))) Complex)
                                (@MulZeroOneClass.toMulOneClass
                                  (Matrix (Fin (@OfNat.ofNat Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
                                    (Fin (@OfNat.ofNat Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))) Complex)
                                  (@instMulZeroOneClassOfSemiring
                                    (Matrix (Fin (@OfNat.ofNat Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
                                      (Fin (@OfNat.ofNat Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))) Complex)
                                    (@Matrix.semiring (Fin (@OfNat.ofNat Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
                                      Complex
                                      (@CommSemiring.toSemiring Complex (@CommRing.toCommSemiring Complex Complex.commRing))
                                      (Fin.fintype (@OfNat.ofNat Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
                                      (instDecidableEqFin (@OfNat.ofNat Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))))))))
                            (@Matrix.unitaryGroup (Fin (@OfNat.ofNat Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
                              (instDecidableEqFin (@OfNat.ofNat Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
                              (Fin.fintype (@OfNat.ofNat Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))) Complex
                              Complex.commRing Complex.instStarRing)
                            x)
                        (@HMul.hMul UpperTheory.Reformulated.B.Gwa7.U2 UpperTheory.Reformulated.B.Gwa7.U2 UpperTheory.Reformulated.B.Gwa7.U2
                          (@instHMul UpperTheory.Reformulated.B.Gwa7.U2
                            (@Submonoid.mul
                              (Matrix (Fin (@OfNat.ofNat Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
                                (Fin (@OfNat.ofNat Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))) Complex)
                              (@MulZeroOneClass.toMulOneClass
                                (Matrix (Fin (@OfNat.ofNat Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
                                  (Fin (@OfNat.ofNat Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))) Complex)
                                (@instMulZeroOneClassOfSemiring
                                  (Matrix (Fin (@OfNat.ofNat Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
                                    (Fin (@OfNat.ofNat Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))) Complex)
                                  (@Matrix.semiring (Fin (@OfNat.ofNat Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))) Complex
                                    (@CommSemiring.toSemiring Complex (@CommRing.toCommSemiring Complex Complex.commRing))
                                    (Fin.fintype (@OfNat.ofNat Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
                                    (instDecidableEqFin (@OfNat.ofNat Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))))))
                              (@Matrix.unitaryGroup (Fin (@OfNat.ofNat Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
                                (instDecidableEqFin (@OfNat.ofNat Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
                                (Fin.fintype (@OfNat.ofNat Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))) Complex
                                Complex.commRing Complex.instStarRing)))
                          (@HMul.hMul UpperTheory.Reformulated.B.Gwa7.U2 UpperTheory.Reformulated.B.Gwa7.U2 UpperTheory.Reformulated.B.Gwa7.U2
                            (@instHMul UpperTheory.Reformulated.B.Gwa7.U2
                              (@Submonoid.mul
                                (Matrix (Fin (@OfNat.ofNat Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
                                  (Fin (@OfNat.ofNat Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))) Complex)
                                (@MulZeroOneClass.toMulOneClass
                                  (Matrix (Fin (@OfNat.ofNat Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
                                    (Fin (@OfNat.ofNat Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))) Complex)
                                  (@instMulZeroOneClassOfSemiring
                                    (Matrix (Fin (@OfNat.ofNat Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
                                      (Fin (@OfNat.ofNat Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))) Complex)
                                    (@Matrix.semiring (Fin (@OfNat.ofNat Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
                                      Complex
                                      (@CommSemiring.toSemiring Complex (@CommRing.toCommSemiring Complex Complex.commRing))
                                      (Fin.fintype (@OfNat.ofNat Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
                                      (instDecidableEqFin (@OfNat.ofNat Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))))))
                                (@Matrix.unitaryGroup (Fin (@OfNat.ofNat Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
                                  (instDecidableEqFin (@OfNat.ofNat Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
                                  (Fin.fintype (@OfNat.ofNat Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))) Complex
                                  Complex.commRing Complex.instStarRing)))
                            l₁ k)
                          l₂)
                        (@OfNat.ofNat (Fin (@OfNat.ofNat Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))) (nat_lit 0)
                          (@Fin.instOfNat (@OfNat.ofNat Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))
                            (@Nat.instNeZeroSucc (@OfNat.ofNat Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))) (nat_lit 0)))
                        (@OfNat.ofNat (Fin (@OfNat.ofNat Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))) (nat_lit 0)
                          (@Fin.instOfNat (@OfNat.ofNat Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))
                            (@Nat.instNeZeroSucc (@OfNat.ofNat Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))) (nat_lit 0))))
                      n)
                    (@HPow.hPow Complex Int Complex
                      (@instHPow Complex Int (@ZPow.toPow Complex (@DivInvMonoid.toZPow Complex Complex.instDivInvMonoid)))
                      (@Matrix.det (Fin (@OfNat.ofNat Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
                        (instDecidableEqFin (@OfNat.ofNat Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
                        (Fin.fintype (@OfNat.ofNat Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))) Complex Complex.commRing
                        (@Subtype.val
                          (Matrix (Fin (@OfNat.ofNat Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
                            (Fin (@OfNat.ofNat Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))) Complex)
                          (fun
                              (x :
                                Matrix (Fin (@OfNat.ofNat Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
                                  (Fin (@OfNat.ofNat Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))) Complex) ↦
                            @Membership.mem
                              (Matrix (Fin (@OfNat.ofNat Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
                                (Fin (@OfNat.ofNat Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))) Complex)
                              (@Submonoid
                                (Matrix (Fin (@OfNat.ofNat Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
                                  (Fin (@OfNat.ofNat Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))) Complex)
                                (@MulZeroOneClass.toMulOneClass
                                  (Matrix (Fin (@OfNat.ofNat Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
                                    (Fin (@OfNat.ofNat Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))) Complex)
                                  (@instMulZeroOneClassOfSemiring
                                    (Matrix (Fin (@OfNat.ofNat Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
                                      (Fin (@OfNat.ofNat Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))) Complex)
                                    (@Matrix.semiring (Fin (@OfNat.ofNat Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
                                      Complex
                                      (@CommSemiring.toSemiring Complex (@CommRing.toCommSemiring Complex Complex.commRing))
                                      (Fin.fintype (@OfNat.ofNat Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
                                      (instDecidableEqFin (@OfNat.ofNat Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))))))
                              (@SetLike.instMembership
                                (@Submonoid
                                  (Matrix (Fin (@OfNat.ofNat Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
                                    (Fin (@OfNat.ofNat Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))) Complex)
                                  (@MulZeroOneClass.toMulOneClass
                                    (Matrix (Fin (@OfNat.ofNat Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
                                      (Fin (@OfNat.ofNat Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))) Complex)
                                    (@instMulZeroOneClassOfSemiring
                                      (Matrix (Fin (@OfNat.ofNat Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
                                        (Fin (@OfNat.ofNat Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))) Complex)
                                      (@Matrix.semiring (Fin (@OfNat.ofNat Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
                                        Complex
                                        (@CommSemiring.toSemiring Complex
                                          (@CommRing.toCommSemiring Complex Complex.commRing))
                                        (Fin.fintype (@OfNat.ofNat Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
                                        (instDecidableEqFin (@OfNat.ofNat Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))))))
                                (Matrix (Fin (@OfNat.ofNat Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
                                  (Fin (@OfNat.ofNat Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))) Complex)
                                (@Submonoid.instSetLike
                                  (Matrix (Fin (@OfNat.ofNat Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
                                    (Fin (@OfNat.ofNat Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))) Complex)
                                  (@MulZeroOneClass.toMulOneClass
                                    (Matrix (Fin (@OfNat.ofNat Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
                                      (Fin (@OfNat.ofNat Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))) Complex)
                                    (@instMulZeroOneClassOfSemiring
                                      (Matrix (Fin (@OfNat.ofNat Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
                                        (Fin (@OfNat.ofNat Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))) Complex)
                                      (@Matrix.semiring (Fin (@OfNat.ofNat Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
                                        Complex
                                        (@CommSemiring.toSemiring Complex
                                          (@CommRing.toCommSemiring Complex Complex.commRing))
                                        (Fin.fintype (@OfNat.ofNat Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
                                        (instDecidableEqFin (@OfNat.ofNat Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))))))))
                              (@Matrix.unitaryGroup (Fin (@OfNat.ofNat Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
                                (instDecidableEqFin (@OfNat.ofNat Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
                                (Fin.fintype (@OfNat.ofNat Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))) Complex
                                Complex.commRing Complex.instStarRing)
                              x)
                          k))
                      q))
                  (g k))
              (@OfNat.ofNat Complex (nat_lit 0) (@Zero.toOfNat0 Complex Complex.instZero))) →
          @Eq (UpperTheory.Reformulated.B.Gwa7.U2 → Complex) g
            (@OfNat.ofNat (UpperTheory.Reformulated.B.Gwa7.U2 → Complex) (nat_lit 0)
              (@Zero.toOfNat0 (UpperTheory.Reformulated.B.Gwa7.U2 → Complex)
                (@Pi.instZero UpperTheory.Reformulated.B.Gwa7.U2 (fun (a : UpperTheory.Reformulated.B.Gwa7.U2) ↦ Complex) fun (i : UpperTheory.Reformulated.B.Gwa7.U2) ↦
                  Complex.instZero))) := by sorry
