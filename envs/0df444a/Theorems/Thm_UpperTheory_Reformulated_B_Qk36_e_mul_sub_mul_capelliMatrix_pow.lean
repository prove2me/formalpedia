-- Prove2me | Theorems.Thm_UpperTheory_Reformulated_B_Qk36_e_mul_sub_mul_capelliMatrix_pow
-- name    : UpperTheory.Reformulated.B.Qk36.e_mul_sub_mul_capelliMatrix_pow
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T19:45:21.595821+00:00
-- url     : https://prove2.me/theorems/df11d33a-953a-4dc5-9925-4e819874d220
-- title:
--   Qk36: e mul sub mul capelli Matrix pow
-- statement:
--   The Qk36 construction uses the e mul sub mul capelli Matrix pow property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicArithmetic/IntegralCasts/CapelliIdentities/EMulSubMulCapelliMatrixPow.lean#L245-L416
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicArithmetic/IntegralCasts/CapelliIdentities/EMulSubMulCapelliMatrixPow.lean#L245-L416

import Mathlib
import Definitions.Def_Development_AutomorphicArithmetic_IntegralCasts_CapelliIdentities_EMulSubMulCapelliMatrixPow
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false

theorem UpperTheory.Reformulated.B.Qk36.e_mul_sub_mul_capelliMatrix_pow :
    ∀ {n : Nat} (a b : Fin n) (k : Nat) (c d : Fin n),
      @Eq (UpperTheory.Reformulated.B.Qk36.U n)
        (@HSub.hSub (UpperTheory.Reformulated.B.Qk36.U n) (UpperTheory.Reformulated.B.Qk36.U n) (UpperTheory.Reformulated.B.Qk36.U n)
          (@instHSub (UpperTheory.Reformulated.B.Qk36.U n)
            (@SubNegMonoid.toSub (UpperTheory.Reformulated.B.Qk36.U n)
              (@AddGroup.toSubNegMonoid (UpperTheory.Reformulated.B.Qk36.U n)
                (@AddGroupWithOne.toAddGroup (UpperTheory.Reformulated.B.Qk36.U n)
                  (@Ring.toAddGroupWithOne (UpperTheory.Reformulated.B.Qk36.U n)
                    (@instRingUniversalEnvelopingAlgebra Complex (UpperTheory.Reformulated.B.Qk36.gl n) Complex.commRing
                      (@LieRing.ofAssociativeRing (UpperTheory.Reformulated.B.Qk36.gl n)
                        (@Matrix.instRing (Fin n) Complex (Fin.fintype n) (instDecidableEqFin n) Complex.instRing))
                      (@LieAlgebra.ofAssociativeAlgebra (UpperTheory.Reformulated.B.Qk36.gl n)
                        (@Matrix.instRing (Fin n) Complex (Fin.fintype n) (instDecidableEqFin n) Complex.instRing) Complex
                        Complex.commRing
                        (@Matrix.instAlgebra (Fin n) Complex Complex (Fin.fintype n) (instDecidableEqFin n)
                          (@CommRing.toCommSemiring Complex Complex.commRing) (@Ring.toSemiring Complex Complex.instRing)
                          (@Algebra.id Complex (@CommRing.toCommSemiring Complex Complex.commRing))))))))))
          (@HMul.hMul (UpperTheory.Reformulated.B.Qk36.U n) (UpperTheory.Reformulated.B.Qk36.U n) (UpperTheory.Reformulated.B.Qk36.U n)
            (@instHMul (UpperTheory.Reformulated.B.Qk36.U n)
              (@Distrib.toMul (UpperTheory.Reformulated.B.Qk36.U n)
                (@instDistribOfSemiring (UpperTheory.Reformulated.B.Qk36.U n)
                  (@Ring.toSemiring (UpperTheory.Reformulated.B.Qk36.U n)
                    (@instRingUniversalEnvelopingAlgebra Complex (UpperTheory.Reformulated.B.Qk36.gl n) Complex.commRing
                      (@LieRing.ofAssociativeRing (UpperTheory.Reformulated.B.Qk36.gl n)
                        (@Matrix.instRing (Fin n) Complex (Fin.fintype n) (instDecidableEqFin n) Complex.instRing))
                      (@LieAlgebra.ofAssociativeAlgebra (UpperTheory.Reformulated.B.Qk36.gl n)
                        (@Matrix.instRing (Fin n) Complex (Fin.fintype n) (instDecidableEqFin n) Complex.instRing) Complex
                        Complex.commRing
                        (@Matrix.instAlgebra (Fin n) Complex Complex (Fin.fintype n) (instDecidableEqFin n)
                          (@CommRing.toCommSemiring Complex Complex.commRing) (@Ring.toSemiring Complex Complex.instRing)
                          (@Algebra.id Complex (@CommRing.toCommSemiring Complex Complex.commRing)))))))))
            (@UpperTheory.Reformulated.B.Qk36.e n (@Prod.mk (Fin n) (Fin n) a b))
            (@HPow.hPow (Matrix (Fin n) (Fin n) (UpperTheory.Reformulated.B.Qk36.U n)) Nat (Matrix (Fin n) (Fin n) (UpperTheory.Reformulated.B.Qk36.U n))
              (@instHPow (Matrix (Fin n) (Fin n) (UpperTheory.Reformulated.B.Qk36.U n)) Nat
                (@NPow.toPow (Matrix (Fin n) (Fin n) (UpperTheory.Reformulated.B.Qk36.U n))
                  (@Monoid.toNPow (Matrix (Fin n) (Fin n) (UpperTheory.Reformulated.B.Qk36.U n))
                    (@Semiring.toMonoid (Matrix (Fin n) (Fin n) (UpperTheory.Reformulated.B.Qk36.U n))
                      (@Matrix.semiring (Fin n) (UpperTheory.Reformulated.B.Qk36.U n)
                        (@Ring.toSemiring (UpperTheory.Reformulated.B.Qk36.U n)
                          (@instRingUniversalEnvelopingAlgebra Complex (UpperTheory.Reformulated.B.Qk36.gl n) Complex.commRing
                            (@LieRing.ofAssociativeRing (UpperTheory.Reformulated.B.Qk36.gl n)
                              (@Matrix.instRing (Fin n) Complex (Fin.fintype n) (instDecidableEqFin n) Complex.instRing))
                            (@LieAlgebra.ofAssociativeAlgebra (UpperTheory.Reformulated.B.Qk36.gl n)
                              (@Matrix.instRing (Fin n) Complex (Fin.fintype n) (instDecidableEqFin n) Complex.instRing)
                              Complex Complex.commRing
                              (@Matrix.instAlgebra (Fin n) Complex Complex (Fin.fintype n) (instDecidableEqFin n)
                                (@CommRing.toCommSemiring Complex Complex.commRing)
                                (@Ring.toSemiring Complex Complex.instRing)
                                (@Algebra.id Complex (@CommRing.toCommSemiring Complex Complex.commRing))))))
                        (Fin.fintype n) (instDecidableEqFin n))))))
              (@UpperTheory.Reformulated.B.Qk36.capelliMatrix n) k c d))
          (@HMul.hMul (UpperTheory.Reformulated.B.Qk36.U n) (UpperTheory.Reformulated.B.Qk36.U n) (UpperTheory.Reformulated.B.Qk36.U n)
            (@instHMul (UpperTheory.Reformulated.B.Qk36.U n)
              (@Distrib.toMul (UpperTheory.Reformulated.B.Qk36.U n)
                (@instDistribOfSemiring (UpperTheory.Reformulated.B.Qk36.U n)
                  (@Ring.toSemiring (UpperTheory.Reformulated.B.Qk36.U n)
                    (@instRingUniversalEnvelopingAlgebra Complex (UpperTheory.Reformulated.B.Qk36.gl n) Complex.commRing
                      (@LieRing.ofAssociativeRing (UpperTheory.Reformulated.B.Qk36.gl n)
                        (@Matrix.instRing (Fin n) Complex (Fin.fintype n) (instDecidableEqFin n) Complex.instRing))
                      (@LieAlgebra.ofAssociativeAlgebra (UpperTheory.Reformulated.B.Qk36.gl n)
                        (@Matrix.instRing (Fin n) Complex (Fin.fintype n) (instDecidableEqFin n) Complex.instRing) Complex
                        Complex.commRing
                        (@Matrix.instAlgebra (Fin n) Complex Complex (Fin.fintype n) (instDecidableEqFin n)
                          (@CommRing.toCommSemiring Complex Complex.commRing) (@Ring.toSemiring Complex Complex.instRing)
                          (@Algebra.id Complex (@CommRing.toCommSemiring Complex Complex.commRing)))))))))
            (@HPow.hPow (Matrix (Fin n) (Fin n) (UpperTheory.Reformulated.B.Qk36.U n)) Nat (Matrix (Fin n) (Fin n) (UpperTheory.Reformulated.B.Qk36.U n))
              (@instHPow (Matrix (Fin n) (Fin n) (UpperTheory.Reformulated.B.Qk36.U n)) Nat
                (@NPow.toPow (Matrix (Fin n) (Fin n) (UpperTheory.Reformulated.B.Qk36.U n))
                  (@Monoid.toNPow (Matrix (Fin n) (Fin n) (UpperTheory.Reformulated.B.Qk36.U n))
                    (@Semiring.toMonoid (Matrix (Fin n) (Fin n) (UpperTheory.Reformulated.B.Qk36.U n))
                      (@Matrix.semiring (Fin n) (UpperTheory.Reformulated.B.Qk36.U n)
                        (@Ring.toSemiring (UpperTheory.Reformulated.B.Qk36.U n)
                          (@instRingUniversalEnvelopingAlgebra Complex (UpperTheory.Reformulated.B.Qk36.gl n) Complex.commRing
                            (@LieRing.ofAssociativeRing (UpperTheory.Reformulated.B.Qk36.gl n)
                              (@Matrix.instRing (Fin n) Complex (Fin.fintype n) (instDecidableEqFin n) Complex.instRing))
                            (@LieAlgebra.ofAssociativeAlgebra (UpperTheory.Reformulated.B.Qk36.gl n)
                              (@Matrix.instRing (Fin n) Complex (Fin.fintype n) (instDecidableEqFin n) Complex.instRing)
                              Complex Complex.commRing
                              (@Matrix.instAlgebra (Fin n) Complex Complex (Fin.fintype n) (instDecidableEqFin n)
                                (@CommRing.toCommSemiring Complex Complex.commRing)
                                (@Ring.toSemiring Complex Complex.instRing)
                                (@Algebra.id Complex (@CommRing.toCommSemiring Complex Complex.commRing))))))
                        (Fin.fintype n) (instDecidableEqFin n))))))
              (@UpperTheory.Reformulated.B.Qk36.capelliMatrix n) k c d)
            (@UpperTheory.Reformulated.B.Qk36.e n (@Prod.mk (Fin n) (Fin n) a b))))
        (@HSub.hSub (UpperTheory.Reformulated.B.Qk36.U n) (UpperTheory.Reformulated.B.Qk36.U n) (UpperTheory.Reformulated.B.Qk36.U n)
          (@instHSub (UpperTheory.Reformulated.B.Qk36.U n)
            (@SubNegMonoid.toSub (UpperTheory.Reformulated.B.Qk36.U n)
              (@AddGroup.toSubNegMonoid (UpperTheory.Reformulated.B.Qk36.U n)
                (@AddGroupWithOne.toAddGroup (UpperTheory.Reformulated.B.Qk36.U n)
                  (@Ring.toAddGroupWithOne (UpperTheory.Reformulated.B.Qk36.U n)
                    (@instRingUniversalEnvelopingAlgebra Complex (UpperTheory.Reformulated.B.Qk36.gl n) Complex.commRing
                      (@LieRing.ofAssociativeRing (UpperTheory.Reformulated.B.Qk36.gl n)
                        (@Matrix.instRing (Fin n) Complex (Fin.fintype n) (instDecidableEqFin n) Complex.instRing))
                      (@LieAlgebra.ofAssociativeAlgebra (UpperTheory.Reformulated.B.Qk36.gl n)
                        (@Matrix.instRing (Fin n) Complex (Fin.fintype n) (instDecidableEqFin n) Complex.instRing) Complex
                        Complex.commRing
                        (@Matrix.instAlgebra (Fin n) Complex Complex (Fin.fintype n) (instDecidableEqFin n)
                          (@CommRing.toCommSemiring Complex Complex.commRing) (@Ring.toSemiring Complex Complex.instRing)
                          (@Algebra.id Complex (@CommRing.toCommSemiring Complex Complex.commRing))))))))))
          (@ite (UpperTheory.Reformulated.B.Qk36.U n) (@Eq (Fin n) b c) (instDecidableEqFin n b c)
            (@HPow.hPow (Matrix (Fin n) (Fin n) (UpperTheory.Reformulated.B.Qk36.U n)) Nat (Matrix (Fin n) (Fin n) (UpperTheory.Reformulated.B.Qk36.U n))
              (@instHPow (Matrix (Fin n) (Fin n) (UpperTheory.Reformulated.B.Qk36.U n)) Nat
                (@NPow.toPow (Matrix (Fin n) (Fin n) (UpperTheory.Reformulated.B.Qk36.U n))
                  (@Monoid.toNPow (Matrix (Fin n) (Fin n) (UpperTheory.Reformulated.B.Qk36.U n))
                    (@Semiring.toMonoid (Matrix (Fin n) (Fin n) (UpperTheory.Reformulated.B.Qk36.U n))
                      (@Matrix.semiring (Fin n) (UpperTheory.Reformulated.B.Qk36.U n)
                        (@Ring.toSemiring (UpperTheory.Reformulated.B.Qk36.U n)
                          (@instRingUniversalEnvelopingAlgebra Complex (UpperTheory.Reformulated.B.Qk36.gl n) Complex.commRing
                            (@LieRing.ofAssociativeRing (UpperTheory.Reformulated.B.Qk36.gl n)
                              (@Matrix.instRing (Fin n) Complex (Fin.fintype n) (instDecidableEqFin n) Complex.instRing))
                            (@LieAlgebra.ofAssociativeAlgebra (UpperTheory.Reformulated.B.Qk36.gl n)
                              (@Matrix.instRing (Fin n) Complex (Fin.fintype n) (instDecidableEqFin n) Complex.instRing)
                              Complex Complex.commRing
                              (@Matrix.instAlgebra (Fin n) Complex Complex (Fin.fintype n) (instDecidableEqFin n)
                                (@CommRing.toCommSemiring Complex Complex.commRing)
                                (@Ring.toSemiring Complex Complex.instRing)
                                (@Algebra.id Complex (@CommRing.toCommSemiring Complex Complex.commRing))))))
                        (Fin.fintype n) (instDecidableEqFin n))))))
              (@UpperTheory.Reformulated.B.Qk36.capelliMatrix n) k a d)
            (@OfNat.ofNat (UpperTheory.Reformulated.B.Qk36.U n) (nat_lit 0)
              (@Zero.toOfNat0 (UpperTheory.Reformulated.B.Qk36.U n)
                (@MulZeroClass.toZero (UpperTheory.Reformulated.B.Qk36.U n)
                  (@instMulZeroClassOfSemiring (UpperTheory.Reformulated.B.Qk36.U n)
                    (@Ring.toSemiring (UpperTheory.Reformulated.B.Qk36.U n)
                      (@instRingUniversalEnvelopingAlgebra Complex (UpperTheory.Reformulated.B.Qk36.gl n) Complex.commRing
                        (@LieRing.ofAssociativeRing (UpperTheory.Reformulated.B.Qk36.gl n)
                          (@Matrix.instRing (Fin n) Complex (Fin.fintype n) (instDecidableEqFin n) Complex.instRing))
                        (@LieAlgebra.ofAssociativeAlgebra (UpperTheory.Reformulated.B.Qk36.gl n)
                          (@Matrix.instRing (Fin n) Complex (Fin.fintype n) (instDecidableEqFin n) Complex.instRing) Complex
                          Complex.commRing
                          (@Matrix.instAlgebra (Fin n) Complex Complex (Fin.fintype n) (instDecidableEqFin n)
                            (@CommRing.toCommSemiring Complex Complex.commRing) (@Ring.toSemiring Complex Complex.instRing)
                            (@Algebra.id Complex (@CommRing.toCommSemiring Complex Complex.commRing)))))))))))
          (@ite (UpperTheory.Reformulated.B.Qk36.U n) (@Eq (Fin n) d a) (instDecidableEqFin n d a)
            (@HPow.hPow (Matrix (Fin n) (Fin n) (UpperTheory.Reformulated.B.Qk36.U n)) Nat (Matrix (Fin n) (Fin n) (UpperTheory.Reformulated.B.Qk36.U n))
              (@instHPow (Matrix (Fin n) (Fin n) (UpperTheory.Reformulated.B.Qk36.U n)) Nat
                (@NPow.toPow (Matrix (Fin n) (Fin n) (UpperTheory.Reformulated.B.Qk36.U n))
                  (@Monoid.toNPow (Matrix (Fin n) (Fin n) (UpperTheory.Reformulated.B.Qk36.U n))
                    (@Semiring.toMonoid (Matrix (Fin n) (Fin n) (UpperTheory.Reformulated.B.Qk36.U n))
                      (@Matrix.semiring (Fin n) (UpperTheory.Reformulated.B.Qk36.U n)
                        (@Ring.toSemiring (UpperTheory.Reformulated.B.Qk36.U n)
                          (@instRingUniversalEnvelopingAlgebra Complex (UpperTheory.Reformulated.B.Qk36.gl n) Complex.commRing
                            (@LieRing.ofAssociativeRing (UpperTheory.Reformulated.B.Qk36.gl n)
                              (@Matrix.instRing (Fin n) Complex (Fin.fintype n) (instDecidableEqFin n) Complex.instRing))
                            (@LieAlgebra.ofAssociativeAlgebra (UpperTheory.Reformulated.B.Qk36.gl n)
                              (@Matrix.instRing (Fin n) Complex (Fin.fintype n) (instDecidableEqFin n) Complex.instRing)
                              Complex Complex.commRing
                              (@Matrix.instAlgebra (Fin n) Complex Complex (Fin.fintype n) (instDecidableEqFin n)
                                (@CommRing.toCommSemiring Complex Complex.commRing)
                                (@Ring.toSemiring Complex Complex.instRing)
                                (@Algebra.id Complex (@CommRing.toCommSemiring Complex Complex.commRing))))))
                        (Fin.fintype n) (instDecidableEqFin n))))))
              (@UpperTheory.Reformulated.B.Qk36.capelliMatrix n) k c b)
            (@OfNat.ofNat (UpperTheory.Reformulated.B.Qk36.U n) (nat_lit 0)
              (@Zero.toOfNat0 (UpperTheory.Reformulated.B.Qk36.U n)
                (@MulZeroClass.toZero (UpperTheory.Reformulated.B.Qk36.U n)
                  (@instMulZeroClassOfSemiring (UpperTheory.Reformulated.B.Qk36.U n)
                    (@Ring.toSemiring (UpperTheory.Reformulated.B.Qk36.U n)
                      (@instRingUniversalEnvelopingAlgebra Complex (UpperTheory.Reformulated.B.Qk36.gl n) Complex.commRing
                        (@LieRing.ofAssociativeRing (UpperTheory.Reformulated.B.Qk36.gl n)
                          (@Matrix.instRing (Fin n) Complex (Fin.fintype n) (instDecidableEqFin n) Complex.instRing))
                        (@LieAlgebra.ofAssociativeAlgebra (UpperTheory.Reformulated.B.Qk36.gl n)
                          (@Matrix.instRing (Fin n) Complex (Fin.fintype n) (instDecidableEqFin n) Complex.instRing) Complex
                          Complex.commRing
                          (@Matrix.instAlgebra (Fin n) Complex Complex (Fin.fintype n) (instDecidableEqFin n)
                            (@CommRing.toCommSemiring Complex Complex.commRing) (@Ring.toSemiring Complex Complex.instRing)
                            (@Algebra.id Complex (@CommRing.toCommSemiring Complex Complex.commRing)))))))))))) := by sorry
