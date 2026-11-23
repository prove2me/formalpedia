-- Prove2me | Theorems.Thm_UpperTheory_Reformulated_B_Re3_hloweq_transfer
-- name    : UpperTheory.Reformulated.B.Re3.hloweq_transfer
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T10:00:33.878101+00:00
-- url     : https://prove2.me/theorems/41b9865f-8710-4deb-ad12-4cf1e61e9f43
-- title:
--   Re3: hloweq transfer
-- statement:
--   The Re3 construction uses the hloweq transfer property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicArithmetic/IntegralCasts/CapelliIdentities/ComplexNormedInstanceCompat.lean#L2492-L3669
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicArithmetic/IntegralCasts/CapelliIdentities/ComplexNormedInstanceCompat.lean#L2492-L3669

import Mathlib
import Definitions.Def_Development_AutomorphicArithmetic_IntegralCasts_CapelliIdentities_ComplexNormedInstanceCompat
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
attribute [local instance] UpperTheory.Reformulated.B.Re3.instMeasurableSpaceUJ

theorem UpperTheory.Reformulated.B.Re3.hloweq_transfer :
    ∀ {n : Nat} {ε : Fin n → Bool} {Λ : Fin n → Real}
      (A :
        @LinearMap Complex Complex Complex.instSemiring Complex.instSemiring
          (@RingHom.id Complex (@Semiring.toNonAssocSemiring Complex Complex.instSemiring)) (@UpperTheory.Reformulated.B.Re3.L2 n ε)
          (@UpperTheory.Reformulated.B.Re3.L2 n ε)
          (@AddCommGroup.toAddCommMonoid (@UpperTheory.Reformulated.B.Re3.L2 n ε)
            (@MeasureTheory.Lp.instAddCommGroup (↥(@UpperTheory.Reformulated.B.Re3.UJ n ε)) Complex
              (UpperTheory.Reformulated.B.Re3.instMeasurableSpaceUJ n ε)
              (@OfNat.ofNat ENNReal (nat_lit 2)
                (@instOfNatAtLeastTwo ENNReal (nat_lit 2)
                  (@AddMonoidWithOne.toNatCast ENNReal
                    (@AddCommMonoidWithOne.toAddMonoidWithOne ENNReal ENNReal.instAddCommMonoidWithOne))
                  UpperTheory.Reformulated.B.Re3.algebra_smulCommClass_complex))
              (@UpperTheory.Reformulated.B.Re3.muG n ε) Complex.instNormedAddCommGroup))
          (@AddCommGroup.toAddCommMonoid (@UpperTheory.Reformulated.B.Re3.L2 n ε)
            (@MeasureTheory.Lp.instAddCommGroup (↥(@UpperTheory.Reformulated.B.Re3.UJ n ε)) Complex
              (UpperTheory.Reformulated.B.Re3.instMeasurableSpaceUJ n ε)
              (@OfNat.ofNat ENNReal (nat_lit 2)
                (@instOfNatAtLeastTwo ENNReal (nat_lit 2)
                  (@AddMonoidWithOne.toNatCast ENNReal
                    (@AddCommMonoidWithOne.toAddMonoidWithOne ENNReal ENNReal.instAddCommMonoidWithOne))
                  UpperTheory.Reformulated.B.Re3.algebra_smulCommClass_complex))
              (@UpperTheory.Reformulated.B.Re3.muG n ε) Complex.instNormedAddCommGroup))
          (@MeasureTheory.Lp.instModule (↥(@UpperTheory.Reformulated.B.Re3.UJ n ε)) Complex Complex
            (UpperTheory.Reformulated.B.Re3.instMeasurableSpaceUJ n ε)
            (@OfNat.ofNat ENNReal (nat_lit 2)
              (@instOfNatAtLeastTwo ENNReal (nat_lit 2)
                (@AddMonoidWithOne.toNatCast ENNReal
                  (@AddCommMonoidWithOne.toAddMonoidWithOne ENNReal ENNReal.instAddCommMonoidWithOne))
                UpperTheory.Reformulated.B.Re3.algebra_smulCommClass_complex))
            (@UpperTheory.Reformulated.B.Re3.muG n ε) Complex.instNormedAddCommGroup
            (@CStarAlgebra.toNormedRing Complex (@CommCStarAlgebra.toCStarAlgebra Complex instCommCStarAlgebraComplex))
            (@Semiring.toModule Complex
              (@Ring.toSemiring Complex
                (@NormedRing.toRing Complex
                  (@CStarAlgebra.toNormedRing Complex
                    (@CommCStarAlgebra.toCStarAlgebra Complex instCommCStarAlgebraComplex)))))
            (@NormedSpace.toIsBoundedSMul Complex Complex Complex.instNormedField
              (@NonUnitalSeminormedRing.toSeminormedAddCommGroup Complex
                (@NonUnitalSeminormedCommRing.toNonUnitalSeminormedRing Complex
                  (@SeminormedCommRing.toNonUnitalSeminormedCommRing Complex
                    (@NormedCommRing.toSeminormedCommRing Complex
                      (@CommCStarAlgebra.toNormedCommRing Complex instCommCStarAlgebraComplex)))))
              (@NonUnitalCStarAlgebra.toNormedSpace Complex
                (@NonUnitalCommCStarAlgebra.toNonUnitalCStarAlgebra Complex
                  (@CommCStarAlgebra.toNonUnitalCommCStarAlgebra Complex instCommCStarAlgebraComplex)))))
          (@MeasureTheory.Lp.instModule (↥(@UpperTheory.Reformulated.B.Re3.UJ n ε)) Complex Complex
            (UpperTheory.Reformulated.B.Re3.instMeasurableSpaceUJ n ε)
            (@OfNat.ofNat ENNReal (nat_lit 2)
              (@instOfNatAtLeastTwo ENNReal (nat_lit 2)
                (@AddMonoidWithOne.toNatCast ENNReal
                  (@AddCommMonoidWithOne.toAddMonoidWithOne ENNReal ENNReal.instAddCommMonoidWithOne))
                UpperTheory.Reformulated.B.Re3.algebra_smulCommClass_complex))
            (@UpperTheory.Reformulated.B.Re3.muG n ε) Complex.instNormedAddCommGroup
            (@CStarAlgebra.toNormedRing Complex (@CommCStarAlgebra.toCStarAlgebra Complex instCommCStarAlgebraComplex))
            (@Semiring.toModule Complex
              (@Ring.toSemiring Complex
                (@NormedRing.toRing Complex
                  (@CStarAlgebra.toNormedRing Complex
                    (@CommCStarAlgebra.toCStarAlgebra Complex instCommCStarAlgebraComplex)))))
            (@NormedSpace.toIsBoundedSMul Complex Complex Complex.instNormedField
              (@NonUnitalSeminormedRing.toSeminormedAddCommGroup Complex
                (@NonUnitalSeminormedCommRing.toNonUnitalSeminormedRing Complex
                  (@SeminormedCommRing.toNonUnitalSeminormedCommRing Complex
                    (@NormedCommRing.toSeminormedCommRing Complex
                      (@CommCStarAlgebra.toNormedCommRing Complex instCommCStarAlgebraComplex)))))
              (@NonUnitalCStarAlgebra.toNormedSpace Complex
                (@NonUnitalCommCStarAlgebra.toNonUnitalCStarAlgebra Complex
                  (@CommCStarAlgebra.toNonUnitalCommCStarAlgebra Complex instCommCStarAlgebraComplex)))))),
      (∀ (k : Matrix (Fin n) (Fin n) Complex),
          @Membership.mem (Matrix (Fin n) (Fin n) Complex) (Set (Matrix (Fin n) (Fin n) Complex))
              (@Set.instMembership (Matrix (Fin n) (Fin n) Complex)) (@UpperTheory.Reformulated.B.Re3.Kset n ε) k →
            ∀ (x : @UpperTheory.Reformulated.B.Re3.L2 n ε),
              @Eq (@UpperTheory.Reformulated.B.Re3.L2 n ε)
                (@DFunLike.coe
                  (@LinearMap Complex Complex Complex.instSemiring Complex.instSemiring
                    (@RingHom.id Complex (@Semiring.toNonAssocSemiring Complex Complex.instSemiring))
                    (@UpperTheory.Reformulated.B.Re3.L2 n ε) (@UpperTheory.Reformulated.B.Re3.L2 n ε)
                    (@AddCommGroup.toAddCommMonoid (@UpperTheory.Reformulated.B.Re3.L2 n ε)
                      (@MeasureTheory.Lp.instAddCommGroup (↥(@UpperTheory.Reformulated.B.Re3.UJ n ε)) Complex
                        (UpperTheory.Reformulated.B.Re3.instMeasurableSpaceUJ n ε)
                        (@OfNat.ofNat ENNReal (nat_lit 2)
                          (@instOfNatAtLeastTwo ENNReal (nat_lit 2)
                            (@AddMonoidWithOne.toNatCast ENNReal
                              (@AddCommMonoidWithOne.toAddMonoidWithOne ENNReal ENNReal.instAddCommMonoidWithOne))
                            UpperTheory.Reformulated.B.Re3.algebra_smulCommClass_complex))
                        (@UpperTheory.Reformulated.B.Re3.muG n ε) Complex.instNormedAddCommGroup))
                    (@AddCommGroup.toAddCommMonoid (@UpperTheory.Reformulated.B.Re3.L2 n ε)
                      (@MeasureTheory.Lp.instAddCommGroup (↥(@UpperTheory.Reformulated.B.Re3.UJ n ε)) Complex
                        (UpperTheory.Reformulated.B.Re3.instMeasurableSpaceUJ n ε)
                        (@OfNat.ofNat ENNReal (nat_lit 2)
                          (@instOfNatAtLeastTwo ENNReal (nat_lit 2)
                            (@AddMonoidWithOne.toNatCast ENNReal
                              (@AddCommMonoidWithOne.toAddMonoidWithOne ENNReal ENNReal.instAddCommMonoidWithOne))
                            UpperTheory.Reformulated.B.Re3.algebra_smulCommClass_complex))
                        (@UpperTheory.Reformulated.B.Re3.muG n ε) Complex.instNormedAddCommGroup))
                    (@MeasureTheory.Lp.instModule (↥(@UpperTheory.Reformulated.B.Re3.UJ n ε)) Complex Complex
                      (UpperTheory.Reformulated.B.Re3.instMeasurableSpaceUJ n ε)
                      (@OfNat.ofNat ENNReal (nat_lit 2)
                        (@instOfNatAtLeastTwo ENNReal (nat_lit 2)
                          (@AddMonoidWithOne.toNatCast ENNReal
                            (@AddCommMonoidWithOne.toAddMonoidWithOne ENNReal ENNReal.instAddCommMonoidWithOne))
                          UpperTheory.Reformulated.B.Re3.algebra_smulCommClass_complex))
                      (@UpperTheory.Reformulated.B.Re3.muG n ε) Complex.instNormedAddCommGroup
                      (@CStarAlgebra.toNormedRing Complex
                        (@CommCStarAlgebra.toCStarAlgebra Complex instCommCStarAlgebraComplex))
                      (@Semiring.toModule Complex
                        (@Ring.toSemiring Complex
                          (@NormedRing.toRing Complex
                            (@CStarAlgebra.toNormedRing Complex
                              (@CommCStarAlgebra.toCStarAlgebra Complex instCommCStarAlgebraComplex)))))
                      (@NormedSpace.toIsBoundedSMul Complex Complex Complex.instNormedField
                        (@NonUnitalSeminormedRing.toSeminormedAddCommGroup Complex
                          (@NonUnitalSeminormedCommRing.toNonUnitalSeminormedRing Complex
                            (@SeminormedCommRing.toNonUnitalSeminormedCommRing Complex
                              (@NormedCommRing.toSeminormedCommRing Complex
                                (@CommCStarAlgebra.toNormedCommRing Complex instCommCStarAlgebraComplex)))))
                        (@NonUnitalCStarAlgebra.toNormedSpace Complex
                          (@NonUnitalCommCStarAlgebra.toNonUnitalCStarAlgebra Complex
                            (@CommCStarAlgebra.toNonUnitalCommCStarAlgebra Complex instCommCStarAlgebraComplex)))))
                    (@MeasureTheory.Lp.instModule (↥(@UpperTheory.Reformulated.B.Re3.UJ n ε)) Complex Complex
                      (UpperTheory.Reformulated.B.Re3.instMeasurableSpaceUJ n ε)
                      (@OfNat.ofNat ENNReal (nat_lit 2)
                        (@instOfNatAtLeastTwo ENNReal (nat_lit 2)
                          (@AddMonoidWithOne.toNatCast ENNReal
                            (@AddCommMonoidWithOne.toAddMonoidWithOne ENNReal ENNReal.instAddCommMonoidWithOne))
                          UpperTheory.Reformulated.B.Re3.algebra_smulCommClass_complex))
                      (@UpperTheory.Reformulated.B.Re3.muG n ε) Complex.instNormedAddCommGroup
                      (@CStarAlgebra.toNormedRing Complex
                        (@CommCStarAlgebra.toCStarAlgebra Complex instCommCStarAlgebraComplex))
                      (@Semiring.toModule Complex
                        (@Ring.toSemiring Complex
                          (@NormedRing.toRing Complex
                            (@CStarAlgebra.toNormedRing Complex
                              (@CommCStarAlgebra.toCStarAlgebra Complex instCommCStarAlgebraComplex)))))
                      (@NormedSpace.toIsBoundedSMul Complex Complex Complex.instNormedField
                        (@NonUnitalSeminormedRing.toSeminormedAddCommGroup Complex
                          (@NonUnitalSeminormedCommRing.toNonUnitalSeminormedRing Complex
                            (@SeminormedCommRing.toNonUnitalSeminormedCommRing Complex
                              (@NormedCommRing.toSeminormedCommRing Complex
                                (@CommCStarAlgebra.toNormedCommRing Complex instCommCStarAlgebraComplex)))))
                        (@NonUnitalCStarAlgebra.toNormedSpace Complex
                          (@NonUnitalCommCStarAlgebra.toNonUnitalCStarAlgebra Complex
                            (@CommCStarAlgebra.toNonUnitalCommCStarAlgebra Complex instCommCStarAlgebraComplex))))))
                  (@UpperTheory.Reformulated.B.Re3.L2 n ε) (fun (x : @UpperTheory.Reformulated.B.Re3.L2 n ε) ↦ @UpperTheory.Reformulated.B.Re3.L2 n ε)
                  (@LinearMap.instFunLike Complex Complex (@UpperTheory.Reformulated.B.Re3.L2 n ε) (@UpperTheory.Reformulated.B.Re3.L2 n ε)
                    Complex.instSemiring Complex.instSemiring
                    (@AddCommGroup.toAddCommMonoid (@UpperTheory.Reformulated.B.Re3.L2 n ε)
                      (@MeasureTheory.Lp.instAddCommGroup (↥(@UpperTheory.Reformulated.B.Re3.UJ n ε)) Complex
                        (UpperTheory.Reformulated.B.Re3.instMeasurableSpaceUJ n ε)
                        (@OfNat.ofNat ENNReal (nat_lit 2)
                          (@instOfNatAtLeastTwo ENNReal (nat_lit 2)
                            (@AddMonoidWithOne.toNatCast ENNReal
                              (@AddCommMonoidWithOne.toAddMonoidWithOne ENNReal ENNReal.instAddCommMonoidWithOne))
                            UpperTheory.Reformulated.B.Re3.algebra_smulCommClass_complex))
                        (@UpperTheory.Reformulated.B.Re3.muG n ε) Complex.instNormedAddCommGroup))
                    (@AddCommGroup.toAddCommMonoid (@UpperTheory.Reformulated.B.Re3.L2 n ε)
                      (@MeasureTheory.Lp.instAddCommGroup (↥(@UpperTheory.Reformulated.B.Re3.UJ n ε)) Complex
                        (UpperTheory.Reformulated.B.Re3.instMeasurableSpaceUJ n ε)
                        (@OfNat.ofNat ENNReal (nat_lit 2)
                          (@instOfNatAtLeastTwo ENNReal (nat_lit 2)
                            (@AddMonoidWithOne.toNatCast ENNReal
                              (@AddCommMonoidWithOne.toAddMonoidWithOne ENNReal ENNReal.instAddCommMonoidWithOne))
                            UpperTheory.Reformulated.B.Re3.algebra_smulCommClass_complex))
                        (@UpperTheory.Reformulated.B.Re3.muG n ε) Complex.instNormedAddCommGroup))
                    (@MeasureTheory.Lp.instModule (↥(@UpperTheory.Reformulated.B.Re3.UJ n ε)) Complex Complex
                      (UpperTheory.Reformulated.B.Re3.instMeasurableSpaceUJ n ε)
                      (@OfNat.ofNat ENNReal (nat_lit 2)
                        (@instOfNatAtLeastTwo ENNReal (nat_lit 2)
                          (@AddMonoidWithOne.toNatCast ENNReal
                            (@AddCommMonoidWithOne.toAddMonoidWithOne ENNReal ENNReal.instAddCommMonoidWithOne))
                          UpperTheory.Reformulated.B.Re3.algebra_smulCommClass_complex))
                      (@UpperTheory.Reformulated.B.Re3.muG n ε) Complex.instNormedAddCommGroup
                      (@CStarAlgebra.toNormedRing Complex
                        (@CommCStarAlgebra.toCStarAlgebra Complex instCommCStarAlgebraComplex))
                      (@Semiring.toModule Complex
                        (@Ring.toSemiring Complex
                          (@NormedRing.toRing Complex
                            (@CStarAlgebra.toNormedRing Complex
                              (@CommCStarAlgebra.toCStarAlgebra Complex instCommCStarAlgebraComplex)))))
                      (@NormedSpace.toIsBoundedSMul Complex Complex Complex.instNormedField
                        (@NonUnitalSeminormedRing.toSeminormedAddCommGroup Complex
                          (@NonUnitalSeminormedCommRing.toNonUnitalSeminormedRing Complex
                            (@SeminormedCommRing.toNonUnitalSeminormedCommRing Complex
                              (@NormedCommRing.toSeminormedCommRing Complex
                                (@CommCStarAlgebra.toNormedCommRing Complex instCommCStarAlgebraComplex)))))
                        (@NonUnitalCStarAlgebra.toNormedSpace Complex
                          (@NonUnitalCommCStarAlgebra.toNonUnitalCStarAlgebra Complex
                            (@CommCStarAlgebra.toNonUnitalCommCStarAlgebra Complex instCommCStarAlgebraComplex)))))
                    (@MeasureTheory.Lp.instModule (↥(@UpperTheory.Reformulated.B.Re3.UJ n ε)) Complex Complex
                      (UpperTheory.Reformulated.B.Re3.instMeasurableSpaceUJ n ε)
                      (@OfNat.ofNat ENNReal (nat_lit 2)
                        (@instOfNatAtLeastTwo ENNReal (nat_lit 2)
                          (@AddMonoidWithOne.toNatCast ENNReal
                            (@AddCommMonoidWithOne.toAddMonoidWithOne ENNReal ENNReal.instAddCommMonoidWithOne))
                          UpperTheory.Reformulated.B.Re3.algebra_smulCommClass_complex))
                      (@UpperTheory.Reformulated.B.Re3.muG n ε) Complex.instNormedAddCommGroup
                      (@CStarAlgebra.toNormedRing Complex
                        (@CommCStarAlgebra.toCStarAlgebra Complex instCommCStarAlgebraComplex))
                      (@Semiring.toModule Complex
                        (@Ring.toSemiring Complex
                          (@NormedRing.toRing Complex
                            (@CStarAlgebra.toNormedRing Complex
                              (@CommCStarAlgebra.toCStarAlgebra Complex instCommCStarAlgebraComplex)))))
                      (@NormedSpace.toIsBoundedSMul Complex Complex Complex.instNormedField
                        (@NonUnitalSeminormedRing.toSeminormedAddCommGroup Complex
                          (@NonUnitalSeminormedCommRing.toNonUnitalSeminormedRing Complex
                            (@SeminormedCommRing.toNonUnitalSeminormedCommRing Complex
                              (@NormedCommRing.toSeminormedCommRing Complex
                                (@CommCStarAlgebra.toNormedCommRing Complex instCommCStarAlgebraComplex)))))
                        (@NonUnitalCStarAlgebra.toNormedSpace Complex
                          (@NonUnitalCommCStarAlgebra.toNonUnitalCStarAlgebra Complex
                            (@CommCStarAlgebra.toNonUnitalCommCStarAlgebra Complex instCommCStarAlgebraComplex)))))
                    (@RingHom.id Complex (@Semiring.toNonAssocSemiring Complex Complex.instSemiring)))
                  A
                  (@DFunLike.coe
                    (@ContinuousLinearMap Complex Complex Complex.instSemiring Complex.instSemiring
                      (@RingHom.id Complex (@Semiring.toNonAssocSemiring Complex Complex.instSemiring))
                      (@UpperTheory.Reformulated.B.Re3.L2 n ε)
                      (@UniformSpace.toTopologicalSpace (@UpperTheory.Reformulated.B.Re3.L2 n ε)
                        (@PseudoMetricSpace.toUniformSpace (@UpperTheory.Reformulated.B.Re3.L2 n ε)
                          (@SeminormedAddCommGroup.toPseudoMetricSpace (@UpperTheory.Reformulated.B.Re3.L2 n ε)
                            (@NormedAddCommGroup.toSeminormedAddCommGroup (@UpperTheory.Reformulated.B.Re3.L2 n ε)
                              (@MeasureTheory.Lp.instNormedAddCommGroup (↥(@UpperTheory.Reformulated.B.Re3.UJ n ε)) Complex
                                (UpperTheory.Reformulated.B.Re3.instMeasurableSpaceUJ n ε)
                                (@OfNat.ofNat ENNReal (nat_lit 2)
                                  (@instOfNatAtLeastTwo ENNReal (nat_lit 2)
                                    (@AddMonoidWithOne.toNatCast ENNReal
                                      (@AddCommMonoidWithOne.toAddMonoidWithOne ENNReal ENNReal.instAddCommMonoidWithOne))
                                    UpperTheory.Reformulated.B.Re3.algebra_smulCommClass_complex))
                                (@UpperTheory.Reformulated.B.Re3.muG n ε) Complex.instNormedAddCommGroup fact_one_le_two_ennreal)))))
                      (@AddCommGroup.toAddCommMonoid (@UpperTheory.Reformulated.B.Re3.L2 n ε)
                        (@MeasureTheory.Lp.instAddCommGroup (↥(@UpperTheory.Reformulated.B.Re3.UJ n ε)) Complex
                          (UpperTheory.Reformulated.B.Re3.instMeasurableSpaceUJ n ε)
                          (@OfNat.ofNat ENNReal (nat_lit 2)
                            (@instOfNatAtLeastTwo ENNReal (nat_lit 2)
                              (@AddMonoidWithOne.toNatCast ENNReal
                                (@AddCommMonoidWithOne.toAddMonoidWithOne ENNReal ENNReal.instAddCommMonoidWithOne))
                              UpperTheory.Reformulated.B.Re3.algebra_smulCommClass_complex))
                          (@UpperTheory.Reformulated.B.Re3.muG n ε) Complex.instNormedAddCommGroup))
                      (@UpperTheory.Reformulated.B.Re3.L2 n ε)
                      (@UniformSpace.toTopologicalSpace (@UpperTheory.Reformulated.B.Re3.L2 n ε)
                        (@PseudoMetricSpace.toUniformSpace (@UpperTheory.Reformulated.B.Re3.L2 n ε)
                          (@SeminormedAddCommGroup.toPseudoMetricSpace (@UpperTheory.Reformulated.B.Re3.L2 n ε)
                            (@NormedAddCommGroup.toSeminormedAddCommGroup (@UpperTheory.Reformulated.B.Re3.L2 n ε)
                              (@MeasureTheory.Lp.instNormedAddCommGroup (↥(@UpperTheory.Reformulated.B.Re3.UJ n ε)) Complex
                                (UpperTheory.Reformulated.B.Re3.instMeasurableSpaceUJ n ε)
                                (@OfNat.ofNat ENNReal (nat_lit 2)
                                  (@instOfNatAtLeastTwo ENNReal (nat_lit 2)
                                    (@AddMonoidWithOne.toNatCast ENNReal
                                      (@AddCommMonoidWithOne.toAddMonoidWithOne ENNReal ENNReal.instAddCommMonoidWithOne))
                                    UpperTheory.Reformulated.B.Re3.algebra_smulCommClass_complex))
                                (@UpperTheory.Reformulated.B.Re3.muG n ε) Complex.instNormedAddCommGroup fact_one_le_two_ennreal)))))
                      (@AddCommGroup.toAddCommMonoid (@UpperTheory.Reformulated.B.Re3.L2 n ε)
                        (@MeasureTheory.Lp.instAddCommGroup (↥(@UpperTheory.Reformulated.B.Re3.UJ n ε)) Complex
                          (UpperTheory.Reformulated.B.Re3.instMeasurableSpaceUJ n ε)
                          (@OfNat.ofNat ENNReal (nat_lit 2)
                            (@instOfNatAtLeastTwo ENNReal (nat_lit 2)
                              (@AddMonoidWithOne.toNatCast ENNReal
                                (@AddCommMonoidWithOne.toAddMonoidWithOne ENNReal ENNReal.instAddCommMonoidWithOne))
                              UpperTheory.Reformulated.B.Re3.algebra_smulCommClass_complex))
                          (@UpperTheory.Reformulated.B.Re3.muG n ε) Complex.instNormedAddCommGroup))
                      (@MeasureTheory.Lp.instModule (↥(@UpperTheory.Reformulated.B.Re3.UJ n ε)) Complex Complex
                        (UpperTheory.Reformulated.B.Re3.instMeasurableSpaceUJ n ε)
                        (@OfNat.ofNat ENNReal (nat_lit 2)
                          (@instOfNatAtLeastTwo ENNReal (nat_lit 2)
                            (@AddMonoidWithOne.toNatCast ENNReal
                              (@AddCommMonoidWithOne.toAddMonoidWithOne ENNReal ENNReal.instAddCommMonoidWithOne))
                            UpperTheory.Reformulated.B.Re3.algebra_smulCommClass_complex))
                        (@UpperTheory.Reformulated.B.Re3.muG n ε) Complex.instNormedAddCommGroup
                        (@CStarAlgebra.toNormedRing Complex
                          (@CommCStarAlgebra.toCStarAlgebra Complex instCommCStarAlgebraComplex))
                        (@Semiring.toModule Complex
                          (@Ring.toSemiring Complex
                            (@NormedRing.toRing Complex
                              (@CStarAlgebra.toNormedRing Complex
                                (@CommCStarAlgebra.toCStarAlgebra Complex instCommCStarAlgebraComplex)))))
                        (@NormedSpace.toIsBoundedSMul Complex Complex Complex.instNormedField
                          (@NonUnitalSeminormedRing.toSeminormedAddCommGroup Complex
                            (@NonUnitalSeminormedCommRing.toNonUnitalSeminormedRing Complex
                              (@SeminormedCommRing.toNonUnitalSeminormedCommRing Complex
                                (@NormedCommRing.toSeminormedCommRing Complex
                                  (@CommCStarAlgebra.toNormedCommRing Complex instCommCStarAlgebraComplex)))))
                          (@NonUnitalCStarAlgebra.toNormedSpace Complex
                            (@NonUnitalCommCStarAlgebra.toNonUnitalCStarAlgebra Complex
                              (@CommCStarAlgebra.toNonUnitalCommCStarAlgebra Complex instCommCStarAlgebraComplex)))))
                      (@MeasureTheory.Lp.instModule (↥(@UpperTheory.Reformulated.B.Re3.UJ n ε)) Complex Complex
                        (UpperTheory.Reformulated.B.Re3.instMeasurableSpaceUJ n ε)
                        (@OfNat.ofNat ENNReal (nat_lit 2)
                          (@instOfNatAtLeastTwo ENNReal (nat_lit 2)
                            (@AddMonoidWithOne.toNatCast ENNReal
                              (@AddCommMonoidWithOne.toAddMonoidWithOne ENNReal ENNReal.instAddCommMonoidWithOne))
                            UpperTheory.Reformulated.B.Re3.algebra_smulCommClass_complex))
                        (@UpperTheory.Reformulated.B.Re3.muG n ε) Complex.instNormedAddCommGroup
                        (@CStarAlgebra.toNormedRing Complex
                          (@CommCStarAlgebra.toCStarAlgebra Complex instCommCStarAlgebraComplex))
                        (@Semiring.toModule Complex
                          (@Ring.toSemiring Complex
                            (@NormedRing.toRing Complex
                              (@CStarAlgebra.toNormedRing Complex
                                (@CommCStarAlgebra.toCStarAlgebra Complex instCommCStarAlgebraComplex)))))
                        (@NormedSpace.toIsBoundedSMul Complex Complex Complex.instNormedField
                          (@NonUnitalSeminormedRing.toSeminormedAddCommGroup Complex
                            (@NonUnitalSeminormedCommRing.toNonUnitalSeminormedRing Complex
                              (@SeminormedCommRing.toNonUnitalSeminormedCommRing Complex
                                (@NormedCommRing.toSeminormedCommRing Complex
                                  (@CommCStarAlgebra.toNormedCommRing Complex instCommCStarAlgebraComplex)))))
                          (@NonUnitalCStarAlgebra.toNormedSpace Complex
                            (@NonUnitalCommCStarAlgebra.toNonUnitalCStarAlgebra Complex
                              (@CommCStarAlgebra.toNonUnitalCommCStarAlgebra Complex instCommCStarAlgebraComplex))))))
                    (@UpperTheory.Reformulated.B.Re3.L2 n ε) (fun (x : @UpperTheory.Reformulated.B.Re3.L2 n ε) ↦ @UpperTheory.Reformulated.B.Re3.L2 n ε)
                    (@ContinuousLinearMap.funLike Complex Complex Complex.instSemiring Complex.instSemiring
                      (@RingHom.id Complex (@Semiring.toNonAssocSemiring Complex Complex.instSemiring))
                      (@UpperTheory.Reformulated.B.Re3.L2 n ε)
                      (@UniformSpace.toTopologicalSpace (@UpperTheory.Reformulated.B.Re3.L2 n ε)
                        (@PseudoMetricSpace.toUniformSpace (@UpperTheory.Reformulated.B.Re3.L2 n ε)
                          (@SeminormedAddCommGroup.toPseudoMetricSpace (@UpperTheory.Reformulated.B.Re3.L2 n ε)
                            (@NormedAddCommGroup.toSeminormedAddCommGroup (@UpperTheory.Reformulated.B.Re3.L2 n ε)
                              (@MeasureTheory.Lp.instNormedAddCommGroup (↥(@UpperTheory.Reformulated.B.Re3.UJ n ε)) Complex
                                (UpperTheory.Reformulated.B.Re3.instMeasurableSpaceUJ n ε)
                                (@OfNat.ofNat ENNReal (nat_lit 2)
                                  (@instOfNatAtLeastTwo ENNReal (nat_lit 2)
                                    (@AddMonoidWithOne.toNatCast ENNReal
                                      (@AddCommMonoidWithOne.toAddMonoidWithOne ENNReal ENNReal.instAddCommMonoidWithOne))
                                    UpperTheory.Reformulated.B.Re3.algebra_smulCommClass_complex))
                                (@UpperTheory.Reformulated.B.Re3.muG n ε) Complex.instNormedAddCommGroup fact_one_le_two_ennreal)))))
                      (@AddCommGroup.toAddCommMonoid (@UpperTheory.Reformulated.B.Re3.L2 n ε)
                        (@MeasureTheory.Lp.instAddCommGroup (↥(@UpperTheory.Reformulated.B.Re3.UJ n ε)) Complex
                          (UpperTheory.Reformulated.B.Re3.instMeasurableSpaceUJ n ε)
                          (@OfNat.ofNat ENNReal (nat_lit 2)
                            (@instOfNatAtLeastTwo ENNReal (nat_lit 2)
                              (@AddMonoidWithOne.toNatCast ENNReal
                                (@AddCommMonoidWithOne.toAddMonoidWithOne ENNReal ENNReal.instAddCommMonoidWithOne))
                              UpperTheory.Reformulated.B.Re3.algebra_smulCommClass_complex))
                          (@UpperTheory.Reformulated.B.Re3.muG n ε) Complex.instNormedAddCommGroup))
                      (@UpperTheory.Reformulated.B.Re3.L2 n ε)
                      (@UniformSpace.toTopologicalSpace (@UpperTheory.Reformulated.B.Re3.L2 n ε)
                        (@PseudoMetricSpace.toUniformSpace (@UpperTheory.Reformulated.B.Re3.L2 n ε)
                          (@SeminormedAddCommGroup.toPseudoMetricSpace (@UpperTheory.Reformulated.B.Re3.L2 n ε)
                            (@NormedAddCommGroup.toSeminormedAddCommGroup (@UpperTheory.Reformulated.B.Re3.L2 n ε)
                              (@MeasureTheory.Lp.instNormedAddCommGroup (↥(@UpperTheory.Reformulated.B.Re3.UJ n ε)) Complex
                                (UpperTheory.Reformulated.B.Re3.instMeasurableSpaceUJ n ε)
                                (@OfNat.ofNat ENNReal (nat_lit 2)
                                  (@instOfNatAtLeastTwo ENNReal (nat_lit 2)
                                    (@AddMonoidWithOne.toNatCast ENNReal
                                      (@AddCommMonoidWithOne.toAddMonoidWithOne ENNReal ENNReal.instAddCommMonoidWithOne))
                                    UpperTheory.Reformulated.B.Re3.algebra_smulCommClass_complex))
                                (@UpperTheory.Reformulated.B.Re3.muG n ε) Complex.instNormedAddCommGroup fact_one_le_two_ennreal)))))
                      (@AddCommGroup.toAddCommMonoid (@UpperTheory.Reformulated.B.Re3.L2 n ε)
                        (@MeasureTheory.Lp.instAddCommGroup (↥(@UpperTheory.Reformulated.B.Re3.UJ n ε)) Complex
                          (UpperTheory.Reformulated.B.Re3.instMeasurableSpaceUJ n ε)
                          (@OfNat.ofNat ENNReal (nat_lit 2)
                            (@instOfNatAtLeastTwo ENNReal (nat_lit 2)
                              (@AddMonoidWithOne.toNatCast ENNReal
                                (@AddCommMonoidWithOne.toAddMonoidWithOne ENNReal ENNReal.instAddCommMonoidWithOne))
                              UpperTheory.Reformulated.B.Re3.algebra_smulCommClass_complex))
                          (@UpperTheory.Reformulated.B.Re3.muG n ε) Complex.instNormedAddCommGroup))
                      (@MeasureTheory.Lp.instModule (↥(@UpperTheory.Reformulated.B.Re3.UJ n ε)) Complex Complex
                        (UpperTheory.Reformulated.B.Re3.instMeasurableSpaceUJ n ε)
                        (@OfNat.ofNat ENNReal (nat_lit 2)
                          (@instOfNatAtLeastTwo ENNReal (nat_lit 2)
                            (@AddMonoidWithOne.toNatCast ENNReal
                              (@AddCommMonoidWithOne.toAddMonoidWithOne ENNReal ENNReal.instAddCommMonoidWithOne))
                            UpperTheory.Reformulated.B.Re3.algebra_smulCommClass_complex))
                        (@UpperTheory.Reformulated.B.Re3.muG n ε) Complex.instNormedAddCommGroup
                        (@CStarAlgebra.toNormedRing Complex
                          (@CommCStarAlgebra.toCStarAlgebra Complex instCommCStarAlgebraComplex))
                        (@Semiring.toModule Complex
                          (@Ring.toSemiring Complex
                            (@NormedRing.toRing Complex
                              (@CStarAlgebra.toNormedRing Complex
                                (@CommCStarAlgebra.toCStarAlgebra Complex instCommCStarAlgebraComplex)))))
                        (@NormedSpace.toIsBoundedSMul Complex Complex Complex.instNormedField
                          (@NonUnitalSeminormedRing.toSeminormedAddCommGroup Complex
                            (@NonUnitalSeminormedCommRing.toNonUnitalSeminormedRing Complex
                              (@SeminormedCommRing.toNonUnitalSeminormedCommRing Complex
                                (@NormedCommRing.toSeminormedCommRing Complex
                                  (@CommCStarAlgebra.toNormedCommRing Complex instCommCStarAlgebraComplex)))))
                          (@NonUnitalCStarAlgebra.toNormedSpace Complex
                            (@NonUnitalCommCStarAlgebra.toNonUnitalCStarAlgebra Complex
                              (@CommCStarAlgebra.toNonUnitalCommCStarAlgebra Complex instCommCStarAlgebraComplex)))))
                      (@MeasureTheory.Lp.instModule (↥(@UpperTheory.Reformulated.B.Re3.UJ n ε)) Complex Complex
                        (UpperTheory.Reformulated.B.Re3.instMeasurableSpaceUJ n ε)
                        (@OfNat.ofNat ENNReal (nat_lit 2)
                          (@instOfNatAtLeastTwo ENNReal (nat_lit 2)
                            (@AddMonoidWithOne.toNatCast ENNReal
                              (@AddCommMonoidWithOne.toAddMonoidWithOne ENNReal ENNReal.instAddCommMonoidWithOne))
                            UpperTheory.Reformulated.B.Re3.algebra_smulCommClass_complex))
                        (@UpperTheory.Reformulated.B.Re3.muG n ε) Complex.instNormedAddCommGroup
                        (@CStarAlgebra.toNormedRing Complex
                          (@CommCStarAlgebra.toCStarAlgebra Complex instCommCStarAlgebraComplex))
                        (@Semiring.toModule Complex
                          (@Ring.toSemiring Complex
                            (@NormedRing.toRing Complex
                              (@CStarAlgebra.toNormedRing Complex
                                (@CommCStarAlgebra.toCStarAlgebra Complex instCommCStarAlgebraComplex)))))
                        (@NormedSpace.toIsBoundedSMul Complex Complex Complex.instNormedField
                          (@NonUnitalSeminormedRing.toSeminormedAddCommGroup Complex
                            (@NonUnitalSeminormedCommRing.toNonUnitalSeminormedRing Complex
                              (@SeminormedCommRing.toNonUnitalSeminormedCommRing Complex
                                (@NormedCommRing.toSeminormedCommRing Complex
                                  (@CommCStarAlgebra.toNormedCommRing Complex instCommCStarAlgebraComplex)))))
                          (@NonUnitalCStarAlgebra.toNormedSpace Complex
                            (@NonUnitalCommCStarAlgebra.toNonUnitalCStarAlgebra Complex
                              (@CommCStarAlgebra.toNonUnitalCommCStarAlgebra Complex instCommCStarAlgebraComplex))))))
                    (@UpperTheory.Reformulated.B.Re3.rreg n ε k) x))
                (@DFunLike.coe
                  (@ContinuousLinearMap Complex Complex Complex.instSemiring Complex.instSemiring
                    (@RingHom.id Complex (@Semiring.toNonAssocSemiring Complex Complex.instSemiring))
                    (@UpperTheory.Reformulated.B.Re3.L2 n ε)
                    (@UniformSpace.toTopologicalSpace (@UpperTheory.Reformulated.B.Re3.L2 n ε)
                      (@PseudoMetricSpace.toUniformSpace (@UpperTheory.Reformulated.B.Re3.L2 n ε)
                        (@SeminormedAddCommGroup.toPseudoMetricSpace (@UpperTheory.Reformulated.B.Re3.L2 n ε)
                          (@NormedAddCommGroup.toSeminormedAddCommGroup (@UpperTheory.Reformulated.B.Re3.L2 n ε)
                            (@MeasureTheory.Lp.instNormedAddCommGroup (↥(@UpperTheory.Reformulated.B.Re3.UJ n ε)) Complex
                              (UpperTheory.Reformulated.B.Re3.instMeasurableSpaceUJ n ε)
                              (@OfNat.ofNat ENNReal (nat_lit 2)
                                (@instOfNatAtLeastTwo ENNReal (nat_lit 2)
                                  (@AddMonoidWithOne.toNatCast ENNReal
                                    (@AddCommMonoidWithOne.toAddMonoidWithOne ENNReal ENNReal.instAddCommMonoidWithOne))
                                  UpperTheory.Reformulated.B.Re3.algebra_smulCommClass_complex))
                              (@UpperTheory.Reformulated.B.Re3.muG n ε) Complex.instNormedAddCommGroup fact_one_le_two_ennreal)))))
                    (@AddCommGroup.toAddCommMonoid (@UpperTheory.Reformulated.B.Re3.L2 n ε)
                      (@MeasureTheory.Lp.instAddCommGroup (↥(@UpperTheory.Reformulated.B.Re3.UJ n ε)) Complex
                        (UpperTheory.Reformulated.B.Re3.instMeasurableSpaceUJ n ε)
                        (@OfNat.ofNat ENNReal (nat_lit 2)
                          (@instOfNatAtLeastTwo ENNReal (nat_lit 2)
                            (@AddMonoidWithOne.toNatCast ENNReal
                              (@AddCommMonoidWithOne.toAddMonoidWithOne ENNReal ENNReal.instAddCommMonoidWithOne))
                            UpperTheory.Reformulated.B.Re3.algebra_smulCommClass_complex))
                        (@UpperTheory.Reformulated.B.Re3.muG n ε) Complex.instNormedAddCommGroup))
                    (@UpperTheory.Reformulated.B.Re3.L2 n ε)
                    (@UniformSpace.toTopologicalSpace (@UpperTheory.Reformulated.B.Re3.L2 n ε)
                      (@PseudoMetricSpace.toUniformSpace (@UpperTheory.Reformulated.B.Re3.L2 n ε)
                        (@SeminormedAddCommGroup.toPseudoMetricSpace (@UpperTheory.Reformulated.B.Re3.L2 n ε)
                          (@NormedAddCommGroup.toSeminormedAddCommGroup (@UpperTheory.Reformulated.B.Re3.L2 n ε)
                            (@MeasureTheory.Lp.instNormedAddCommGroup (↥(@UpperTheory.Reformulated.B.Re3.UJ n ε)) Complex
                              (UpperTheory.Reformulated.B.Re3.instMeasurableSpaceUJ n ε)
                              (@OfNat.ofNat ENNReal (nat_lit 2)
                                (@instOfNatAtLeastTwo ENNReal (nat_lit 2)
                                  (@AddMonoidWithOne.toNatCast ENNReal
                                    (@AddCommMonoidWithOne.toAddMonoidWithOne ENNReal ENNReal.instAddCommMonoidWithOne))
                                  UpperTheory.Reformulated.B.Re3.algebra_smulCommClass_complex))
                              (@UpperTheory.Reformulated.B.Re3.muG n ε) Complex.instNormedAddCommGroup fact_one_le_two_ennreal)))))
                    (@AddCommGroup.toAddCommMonoid (@UpperTheory.Reformulated.B.Re3.L2 n ε)
                      (@MeasureTheory.Lp.instAddCommGroup (↥(@UpperTheory.Reformulated.B.Re3.UJ n ε)) Complex
                        (UpperTheory.Reformulated.B.Re3.instMeasurableSpaceUJ n ε)
                        (@OfNat.ofNat ENNReal (nat_lit 2)
                          (@instOfNatAtLeastTwo ENNReal (nat_lit 2)
                            (@AddMonoidWithOne.toNatCast ENNReal
                              (@AddCommMonoidWithOne.toAddMonoidWithOne ENNReal ENNReal.instAddCommMonoidWithOne))
                            UpperTheory.Reformulated.B.Re3.algebra_smulCommClass_complex))
                        (@UpperTheory.Reformulated.B.Re3.muG n ε) Complex.instNormedAddCommGroup))
                    (@MeasureTheory.Lp.instModule (↥(@UpperTheory.Reformulated.B.Re3.UJ n ε)) Complex Complex
                      (UpperTheory.Reformulated.B.Re3.instMeasurableSpaceUJ n ε)
                      (@OfNat.ofNat ENNReal (nat_lit 2)
                        (@instOfNatAtLeastTwo ENNReal (nat_lit 2)
                          (@AddMonoidWithOne.toNatCast ENNReal
                            (@AddCommMonoidWithOne.toAddMonoidWithOne ENNReal ENNReal.instAddCommMonoidWithOne))
                          UpperTheory.Reformulated.B.Re3.algebra_smulCommClass_complex))
                      (@UpperTheory.Reformulated.B.Re3.muG n ε) Complex.instNormedAddCommGroup
                      (@CStarAlgebra.toNormedRing Complex
                        (@CommCStarAlgebra.toCStarAlgebra Complex instCommCStarAlgebraComplex))
                      (@Semiring.toModule Complex
                        (@Ring.toSemiring Complex
                          (@NormedRing.toRing Complex
                            (@CStarAlgebra.toNormedRing Complex
                              (@CommCStarAlgebra.toCStarAlgebra Complex instCommCStarAlgebraComplex)))))
                      (@NormedSpace.toIsBoundedSMul Complex Complex Complex.instNormedField
                        (@NonUnitalSeminormedRing.toSeminormedAddCommGroup Complex
                          (@NonUnitalSeminormedCommRing.toNonUnitalSeminormedRing Complex
                            (@SeminormedCommRing.toNonUnitalSeminormedCommRing Complex
                              (@NormedCommRing.toSeminormedCommRing Complex
                                (@CommCStarAlgebra.toNormedCommRing Complex instCommCStarAlgebraComplex)))))
                        (@NonUnitalCStarAlgebra.toNormedSpace Complex
                          (@NonUnitalCommCStarAlgebra.toNonUnitalCStarAlgebra Complex
                            (@CommCStarAlgebra.toNonUnitalCommCStarAlgebra Complex instCommCStarAlgebraComplex)))))
                    (@MeasureTheory.Lp.instModule (↥(@UpperTheory.Reformulated.B.Re3.UJ n ε)) Complex Complex
                      (UpperTheory.Reformulated.B.Re3.instMeasurableSpaceUJ n ε)
                      (@OfNat.ofNat ENNReal (nat_lit 2)
                        (@instOfNatAtLeastTwo ENNReal (nat_lit 2)
                          (@AddMonoidWithOne.toNatCast ENNReal
                            (@AddCommMonoidWithOne.toAddMonoidWithOne ENNReal ENNReal.instAddCommMonoidWithOne))
                          UpperTheory.Reformulated.B.Re3.algebra_smulCommClass_complex))
                      (@UpperTheory.Reformulated.B.Re3.muG n ε) Complex.instNormedAddCommGroup
                      (@CStarAlgebra.toNormedRing Complex
                        (@CommCStarAlgebra.toCStarAlgebra Complex instCommCStarAlgebraComplex))
                      (@Semiring.toModule Complex
                        (@Ring.toSemiring Complex
                          (@NormedRing.toRing Complex
                            (@CStarAlgebra.toNormedRing Complex
                              (@CommCStarAlgebra.toCStarAlgebra Complex instCommCStarAlgebraComplex)))))
                      (@NormedSpace.toIsBoundedSMul Complex Complex Complex.instNormedField
                        (@NonUnitalSeminormedRing.toSeminormedAddCommGroup Complex
                          (@NonUnitalSeminormedCommRing.toNonUnitalSeminormedRing Complex
                            (@SeminormedCommRing.toNonUnitalSeminormedCommRing Complex
                              (@NormedCommRing.toSeminormedCommRing Complex
                                (@CommCStarAlgebra.toNormedCommRing Complex instCommCStarAlgebraComplex)))))
                        (@NonUnitalCStarAlgebra.toNormedSpace Complex
                          (@NonUnitalCommCStarAlgebra.toNonUnitalCStarAlgebra Complex
                            (@CommCStarAlgebra.toNonUnitalCommCStarAlgebra Complex instCommCStarAlgebraComplex))))))
                  (@UpperTheory.Reformulated.B.Re3.L2 n ε) (fun (x : @UpperTheory.Reformulated.B.Re3.L2 n ε) ↦ @UpperTheory.Reformulated.B.Re3.L2 n ε)
                  (@ContinuousLinearMap.funLike Complex Complex Complex.instSemiring Complex.instSemiring
                    (@RingHom.id Complex (@Semiring.toNonAssocSemiring Complex Complex.instSemiring))
                    (@UpperTheory.Reformulated.B.Re3.L2 n ε)
                    (@UniformSpace.toTopologicalSpace (@UpperTheory.Reformulated.B.Re3.L2 n ε)
                      (@PseudoMetricSpace.toUniformSpace (@UpperTheory.Reformulated.B.Re3.L2 n ε)
                        (@SeminormedAddCommGroup.toPseudoMetricSpace (@UpperTheory.Reformulated.B.Re3.L2 n ε)
                          (@NormedAddCommGroup.toSeminormedAddCommGroup (@UpperTheory.Reformulated.B.Re3.L2 n ε)
                            (@MeasureTheory.Lp.instNormedAddCommGroup (↥(@UpperTheory.Reformulated.B.Re3.UJ n ε)) Complex
                              (UpperTheory.Reformulated.B.Re3.instMeasurableSpaceUJ n ε)
                              (@OfNat.ofNat ENNReal (nat_lit 2)
                                (@instOfNatAtLeastTwo ENNReal (nat_lit 2)
                                  (@AddMonoidWithOne.toNatCast ENNReal
                                    (@AddCommMonoidWithOne.toAddMonoidWithOne ENNReal ENNReal.instAddCommMonoidWithOne))
                                  UpperTheory.Reformulated.B.Re3.algebra_smulCommClass_complex))
                              (@UpperTheory.Reformulated.B.Re3.muG n ε) Complex.instNormedAddCommGroup fact_one_le_two_ennreal)))))
                    (@AddCommGroup.toAddCommMonoid (@UpperTheory.Reformulated.B.Re3.L2 n ε)
                      (@MeasureTheory.Lp.instAddCommGroup (↥(@UpperTheory.Reformulated.B.Re3.UJ n ε)) Complex
                        (UpperTheory.Reformulated.B.Re3.instMeasurableSpaceUJ n ε)
                        (@OfNat.ofNat ENNReal (nat_lit 2)
                          (@instOfNatAtLeastTwo ENNReal (nat_lit 2)
                            (@AddMonoidWithOne.toNatCast ENNReal
                              (@AddCommMonoidWithOne.toAddMonoidWithOne ENNReal ENNReal.instAddCommMonoidWithOne))
                            UpperTheory.Reformulated.B.Re3.algebra_smulCommClass_complex))
                        (@UpperTheory.Reformulated.B.Re3.muG n ε) Complex.instNormedAddCommGroup))
                    (@UpperTheory.Reformulated.B.Re3.L2 n ε)
                    (@UniformSpace.toTopologicalSpace (@UpperTheory.Reformulated.B.Re3.L2 n ε)
                      (@PseudoMetricSpace.toUniformSpace (@UpperTheory.Reformulated.B.Re3.L2 n ε)
                        (@SeminormedAddCommGroup.toPseudoMetricSpace (@UpperTheory.Reformulated.B.Re3.L2 n ε)
                          (@NormedAddCommGroup.toSeminormedAddCommGroup (@UpperTheory.Reformulated.B.Re3.L2 n ε)
                            (@MeasureTheory.Lp.instNormedAddCommGroup (↥(@UpperTheory.Reformulated.B.Re3.UJ n ε)) Complex
                              (UpperTheory.Reformulated.B.Re3.instMeasurableSpaceUJ n ε)
                              (@OfNat.ofNat ENNReal (nat_lit 2)
                                (@instOfNatAtLeastTwo ENNReal (nat_lit 2)
                                  (@AddMonoidWithOne.toNatCast ENNReal
                                    (@AddCommMonoidWithOne.toAddMonoidWithOne ENNReal ENNReal.instAddCommMonoidWithOne))
                                  UpperTheory.Reformulated.B.Re3.algebra_smulCommClass_complex))
                              (@UpperTheory.Reformulated.B.Re3.muG n ε) Complex.instNormedAddCommGroup fact_one_le_two_ennreal)))))
                    (@AddCommGroup.toAddCommMonoid (@UpperTheory.Reformulated.B.Re3.L2 n ε)
                      (@MeasureTheory.Lp.instAddCommGroup (↥(@UpperTheory.Reformulated.B.Re3.UJ n ε)) Complex
                        (UpperTheory.Reformulated.B.Re3.instMeasurableSpaceUJ n ε)
                        (@OfNat.ofNat ENNReal (nat_lit 2)
                          (@instOfNatAtLeastTwo ENNReal (nat_lit 2)
                            (@AddMonoidWithOne.toNatCast ENNReal
                              (@AddCommMonoidWithOne.toAddMonoidWithOne ENNReal ENNReal.instAddCommMonoidWithOne))
                            UpperTheory.Reformulated.B.Re3.algebra_smulCommClass_complex))
                        (@UpperTheory.Reformulated.B.Re3.muG n ε) Complex.instNormedAddCommGroup))
                    (@MeasureTheory.Lp.instModule (↥(@UpperTheory.Reformulated.B.Re3.UJ n ε)) Complex Complex
                      (UpperTheory.Reformulated.B.Re3.instMeasurableSpaceUJ n ε)
                      (@OfNat.ofNat ENNReal (nat_lit 2)
                        (@instOfNatAtLeastTwo ENNReal (nat_lit 2)
                          (@AddMonoidWithOne.toNatCast ENNReal
                            (@AddCommMonoidWithOne.toAddMonoidWithOne ENNReal ENNReal.instAddCommMonoidWithOne))
                          UpperTheory.Reformulated.B.Re3.algebra_smulCommClass_complex))
                      (@UpperTheory.Reformulated.B.Re3.muG n ε) Complex.instNormedAddCommGroup
                      (@CStarAlgebra.toNormedRing Complex
                        (@CommCStarAlgebra.toCStarAlgebra Complex instCommCStarAlgebraComplex))
                      (@Semiring.toModule Complex
                        (@Ring.toSemiring Complex
                          (@NormedRing.toRing Complex
                            (@CStarAlgebra.toNormedRing Complex
                              (@CommCStarAlgebra.toCStarAlgebra Complex instCommCStarAlgebraComplex)))))
                      (@NormedSpace.toIsBoundedSMul Complex Complex Complex.instNormedField
                        (@NonUnitalSeminormedRing.toSeminormedAddCommGroup Complex
                          (@NonUnitalSeminormedCommRing.toNonUnitalSeminormedRing Complex
                            (@SeminormedCommRing.toNonUnitalSeminormedCommRing Complex
                              (@NormedCommRing.toSeminormedCommRing Complex
                                (@CommCStarAlgebra.toNormedCommRing Complex instCommCStarAlgebraComplex)))))
                        (@NonUnitalCStarAlgebra.toNormedSpace Complex
                          (@NonUnitalCommCStarAlgebra.toNonUnitalCStarAlgebra Complex
                            (@CommCStarAlgebra.toNonUnitalCommCStarAlgebra Complex instCommCStarAlgebraComplex)))))
                    (@MeasureTheory.Lp.instModule (↥(@UpperTheory.Reformulated.B.Re3.UJ n ε)) Complex Complex
                      (UpperTheory.Reformulated.B.Re3.instMeasurableSpaceUJ n ε)
                      (@OfNat.ofNat ENNReal (nat_lit 2)
                        (@instOfNatAtLeastTwo ENNReal (nat_lit 2)
                          (@AddMonoidWithOne.toNatCast ENNReal
                            (@AddCommMonoidWithOne.toAddMonoidWithOne ENNReal ENNReal.instAddCommMonoidWithOne))
                          UpperTheory.Reformulated.B.Re3.algebra_smulCommClass_complex))
                      (@UpperTheory.Reformulated.B.Re3.muG n ε) Complex.instNormedAddCommGroup
                      (@CStarAlgebra.toNormedRing Complex
                        (@CommCStarAlgebra.toCStarAlgebra Complex instCommCStarAlgebraComplex))
                      (@Semiring.toModule Complex
                        (@Ring.toSemiring Complex
                          (@NormedRing.toRing Complex
                            (@CStarAlgebra.toNormedRing Complex
                              (@CommCStarAlgebra.toCStarAlgebra Complex instCommCStarAlgebraComplex)))))
                      (@NormedSpace.toIsBoundedSMul Complex Complex Complex.instNormedField
                        (@NonUnitalSeminormedRing.toSeminormedAddCommGroup Complex
                          (@NonUnitalSeminormedCommRing.toNonUnitalSeminormedRing Complex
                            (@SeminormedCommRing.toNonUnitalSeminormedCommRing Complex
                              (@NormedCommRing.toSeminormedCommRing Complex
                                (@CommCStarAlgebra.toNormedCommRing Complex instCommCStarAlgebraComplex)))))
                        (@NonUnitalCStarAlgebra.toNormedSpace Complex
                          (@NonUnitalCommCStarAlgebra.toNonUnitalCStarAlgebra Complex
                            (@CommCStarAlgebra.toNonUnitalCommCStarAlgebra Complex instCommCStarAlgebraComplex))))))
                  (@UpperTheory.Reformulated.B.Re3.rreg n ε k)
                  (@DFunLike.coe
                    (@LinearMap Complex Complex Complex.instSemiring Complex.instSemiring
                      (@RingHom.id Complex (@Semiring.toNonAssocSemiring Complex Complex.instSemiring))
                      (@UpperTheory.Reformulated.B.Re3.L2 n ε) (@UpperTheory.Reformulated.B.Re3.L2 n ε)
                      (@AddCommGroup.toAddCommMonoid (@UpperTheory.Reformulated.B.Re3.L2 n ε)
                        (@MeasureTheory.Lp.instAddCommGroup (↥(@UpperTheory.Reformulated.B.Re3.UJ n ε)) Complex
                          (UpperTheory.Reformulated.B.Re3.instMeasurableSpaceUJ n ε)
                          (@OfNat.ofNat ENNReal (nat_lit 2)
                            (@instOfNatAtLeastTwo ENNReal (nat_lit 2)
                              (@AddMonoidWithOne.toNatCast ENNReal
                                (@AddCommMonoidWithOne.toAddMonoidWithOne ENNReal ENNReal.instAddCommMonoidWithOne))
                              UpperTheory.Reformulated.B.Re3.algebra_smulCommClass_complex))
                          (@UpperTheory.Reformulated.B.Re3.muG n ε) Complex.instNormedAddCommGroup))
                      (@AddCommGroup.toAddCommMonoid (@UpperTheory.Reformulated.B.Re3.L2 n ε)
                        (@MeasureTheory.Lp.instAddCommGroup (↥(@UpperTheory.Reformulated.B.Re3.UJ n ε)) Complex
                          (UpperTheory.Reformulated.B.Re3.instMeasurableSpaceUJ n ε)
                          (@OfNat.ofNat ENNReal (nat_lit 2)
                            (@instOfNatAtLeastTwo ENNReal (nat_lit 2)
                              (@AddMonoidWithOne.toNatCast ENNReal
                                (@AddCommMonoidWithOne.toAddMonoidWithOne ENNReal ENNReal.instAddCommMonoidWithOne))
                              UpperTheory.Reformulated.B.Re3.algebra_smulCommClass_complex))
                          (@UpperTheory.Reformulated.B.Re3.muG n ε) Complex.instNormedAddCommGroup))
                      (@MeasureTheory.Lp.instModule (↥(@UpperTheory.Reformulated.B.Re3.UJ n ε)) Complex Complex
                        (UpperTheory.Reformulated.B.Re3.instMeasurableSpaceUJ n ε)
                        (@OfNat.ofNat ENNReal (nat_lit 2)
                          (@instOfNatAtLeastTwo ENNReal (nat_lit 2)
                            (@AddMonoidWithOne.toNatCast ENNReal
                              (@AddCommMonoidWithOne.toAddMonoidWithOne ENNReal ENNReal.instAddCommMonoidWithOne))
                            UpperTheory.Reformulated.B.Re3.algebra_smulCommClass_complex))
                        (@UpperTheory.Reformulated.B.Re3.muG n ε) Complex.instNormedAddCommGroup
                        (@CStarAlgebra.toNormedRing Complex
                          (@CommCStarAlgebra.toCStarAlgebra Complex instCommCStarAlgebraComplex))
                        (@Semiring.toModule Complex
                          (@Ring.toSemiring Complex
                            (@NormedRing.toRing Complex
                              (@CStarAlgebra.toNormedRing Complex
                                (@CommCStarAlgebra.toCStarAlgebra Complex instCommCStarAlgebraComplex)))))
                        (@NormedSpace.toIsBoundedSMul Complex Complex Complex.instNormedField
                          (@NonUnitalSeminormedRing.toSeminormedAddCommGroup Complex
                            (@NonUnitalSeminormedCommRing.toNonUnitalSeminormedRing Complex
                              (@SeminormedCommRing.toNonUnitalSeminormedCommRing Complex
                                (@NormedCommRing.toSeminormedCommRing Complex
                                  (@CommCStarAlgebra.toNormedCommRing Complex instCommCStarAlgebraComplex)))))
                          (@NonUnitalCStarAlgebra.toNormedSpace Complex
                            (@NonUnitalCommCStarAlgebra.toNonUnitalCStarAlgebra Complex
                              (@CommCStarAlgebra.toNonUnitalCommCStarAlgebra Complex instCommCStarAlgebraComplex)))))
                      (@MeasureTheory.Lp.instModule (↥(@UpperTheory.Reformulated.B.Re3.UJ n ε)) Complex Complex
                        (UpperTheory.Reformulated.B.Re3.instMeasurableSpaceUJ n ε)
                        (@OfNat.ofNat ENNReal (nat_lit 2)
                          (@instOfNatAtLeastTwo ENNReal (nat_lit 2)
                            (@AddMonoidWithOne.toNatCast ENNReal
                              (@AddCommMonoidWithOne.toAddMonoidWithOne ENNReal ENNReal.instAddCommMonoidWithOne))
                            UpperTheory.Reformulated.B.Re3.algebra_smulCommClass_complex))
                        (@UpperTheory.Reformulated.B.Re3.muG n ε) Complex.instNormedAddCommGroup
                        (@CStarAlgebra.toNormedRing Complex
                          (@CommCStarAlgebra.toCStarAlgebra Complex instCommCStarAlgebraComplex))
                        (@Semiring.toModule Complex
                          (@Ring.toSemiring Complex
                            (@NormedRing.toRing Complex
                              (@CStarAlgebra.toNormedRing Complex
                                (@CommCStarAlgebra.toCStarAlgebra Complex instCommCStarAlgebraComplex)))))
                        (@NormedSpace.toIsBoundedSMul Complex Complex Complex.instNormedField
                          (@NonUnitalSeminormedRing.toSeminormedAddCommGroup Complex
                            (@NonUnitalSeminormedCommRing.toNonUnitalSeminormedRing Complex
                              (@SeminormedCommRing.toNonUnitalSeminormedCommRing Complex
                                (@NormedCommRing.toSeminormedCommRing Complex
                                  (@CommCStarAlgebra.toNormedCommRing Complex instCommCStarAlgebraComplex)))))
                          (@NonUnitalCStarAlgebra.toNormedSpace Complex
                            (@NonUnitalCommCStarAlgebra.toNonUnitalCStarAlgebra Complex
                              (@CommCStarAlgebra.toNonUnitalCommCStarAlgebra Complex instCommCStarAlgebraComplex))))))
                    (@UpperTheory.Reformulated.B.Re3.L2 n ε) (fun (x : @UpperTheory.Reformulated.B.Re3.L2 n ε) ↦ @UpperTheory.Reformulated.B.Re3.L2 n ε)
                    (@LinearMap.instFunLike Complex Complex (@UpperTheory.Reformulated.B.Re3.L2 n ε) (@UpperTheory.Reformulated.B.Re3.L2 n ε)
                      Complex.instSemiring Complex.instSemiring
                      (@AddCommGroup.toAddCommMonoid (@UpperTheory.Reformulated.B.Re3.L2 n ε)
                        (@MeasureTheory.Lp.instAddCommGroup (↥(@UpperTheory.Reformulated.B.Re3.UJ n ε)) Complex
                          (UpperTheory.Reformulated.B.Re3.instMeasurableSpaceUJ n ε)
                          (@OfNat.ofNat ENNReal (nat_lit 2)
                            (@instOfNatAtLeastTwo ENNReal (nat_lit 2)
                              (@AddMonoidWithOne.toNatCast ENNReal
                                (@AddCommMonoidWithOne.toAddMonoidWithOne ENNReal ENNReal.instAddCommMonoidWithOne))
                              UpperTheory.Reformulated.B.Re3.algebra_smulCommClass_complex))
                          (@UpperTheory.Reformulated.B.Re3.muG n ε) Complex.instNormedAddCommGroup))
                      (@AddCommGroup.toAddCommMonoid (@UpperTheory.Reformulated.B.Re3.L2 n ε)
                        (@MeasureTheory.Lp.instAddCommGroup (↥(@UpperTheory.Reformulated.B.Re3.UJ n ε)) Complex
                          (UpperTheory.Reformulated.B.Re3.instMeasurableSpaceUJ n ε)
                          (@OfNat.ofNat ENNReal (nat_lit 2)
                            (@instOfNatAtLeastTwo ENNReal (nat_lit 2)
                              (@AddMonoidWithOne.toNatCast ENNReal
                                (@AddCommMonoidWithOne.toAddMonoidWithOne ENNReal ENNReal.instAddCommMonoidWithOne))
                              UpperTheory.Reformulated.B.Re3.algebra_smulCommClass_complex))
                          (@UpperTheory.Reformulated.B.Re3.muG n ε) Complex.instNormedAddCommGroup))
                      (@MeasureTheory.Lp.instModule (↥(@UpperTheory.Reformulated.B.Re3.UJ n ε)) Complex Complex
                        (UpperTheory.Reformulated.B.Re3.instMeasurableSpaceUJ n ε)
                        (@OfNat.ofNat ENNReal (nat_lit 2)
                          (@instOfNatAtLeastTwo ENNReal (nat_lit 2)
                            (@AddMonoidWithOne.toNatCast ENNReal
                              (@AddCommMonoidWithOne.toAddMonoidWithOne ENNReal ENNReal.instAddCommMonoidWithOne))
                            UpperTheory.Reformulated.B.Re3.algebra_smulCommClass_complex))
                        (@UpperTheory.Reformulated.B.Re3.muG n ε) Complex.instNormedAddCommGroup
                        (@CStarAlgebra.toNormedRing Complex
                          (@CommCStarAlgebra.toCStarAlgebra Complex instCommCStarAlgebraComplex))
                        (@Semiring.toModule Complex
                          (@Ring.toSemiring Complex
                            (@NormedRing.toRing Complex
                              (@CStarAlgebra.toNormedRing Complex
                                (@CommCStarAlgebra.toCStarAlgebra Complex instCommCStarAlgebraComplex)))))
                        (@NormedSpace.toIsBoundedSMul Complex Complex Complex.instNormedField
                          (@NonUnitalSeminormedRing.toSeminormedAddCommGroup Complex
                            (@NonUnitalSeminormedCommRing.toNonUnitalSeminormedRing Complex
                              (@SeminormedCommRing.toNonUnitalSeminormedCommRing Complex
                                (@NormedCommRing.toSeminormedCommRing Complex
                                  (@CommCStarAlgebra.toNormedCommRing Complex instCommCStarAlgebraComplex)))))
                          (@NonUnitalCStarAlgebra.toNormedSpace Complex
                            (@NonUnitalCommCStarAlgebra.toNonUnitalCStarAlgebra Complex
                              (@CommCStarAlgebra.toNonUnitalCommCStarAlgebra Complex instCommCStarAlgebraComplex)))))
                      (@MeasureTheory.Lp.instModule (↥(@UpperTheory.Reformulated.B.Re3.UJ n ε)) Complex Complex
                        (UpperTheory.Reformulated.B.Re3.instMeasurableSpaceUJ n ε)
                        (@OfNat.ofNat ENNReal (nat_lit 2)
                          (@instOfNatAtLeastTwo ENNReal (nat_lit 2)
                            (@AddMonoidWithOne.toNatCast ENNReal
                              (@AddCommMonoidWithOne.toAddMonoidWithOne ENNReal ENNReal.instAddCommMonoidWithOne))
                            UpperTheory.Reformulated.B.Re3.algebra_smulCommClass_complex))
                        (@UpperTheory.Reformulated.B.Re3.muG n ε) Complex.instNormedAddCommGroup
                        (@CStarAlgebra.toNormedRing Complex
                          (@CommCStarAlgebra.toCStarAlgebra Complex instCommCStarAlgebraComplex))
                        (@Semiring.toModule Complex
                          (@Ring.toSemiring Complex
                            (@NormedRing.toRing Complex
                              (@CStarAlgebra.toNormedRing Complex
                                (@CommCStarAlgebra.toCStarAlgebra Complex instCommCStarAlgebraComplex)))))
                        (@NormedSpace.toIsBoundedSMul Complex Complex Complex.instNormedField
                          (@NonUnitalSeminormedRing.toSeminormedAddCommGroup Complex
                            (@NonUnitalSeminormedCommRing.toNonUnitalSeminormedRing Complex
                              (@SeminormedCommRing.toNonUnitalSeminormedCommRing Complex
                                (@NormedCommRing.toSeminormedCommRing Complex
                                  (@CommCStarAlgebra.toNormedCommRing Complex instCommCStarAlgebraComplex)))))
                          (@NonUnitalCStarAlgebra.toNormedSpace Complex
                            (@NonUnitalCommCStarAlgebra.toNonUnitalCStarAlgebra Complex
                              (@CommCStarAlgebra.toNonUnitalCommCStarAlgebra Complex instCommCStarAlgebraComplex)))))
                      (@RingHom.id Complex (@Semiring.toNonAssocSemiring Complex Complex.instSemiring)))
                    A x))) →
        ∀
          {S :
            @Submodule Complex (@UpperTheory.Reformulated.B.Re3.L2 n ε) Complex.instSemiring
              (@AddCommGroup.toAddCommMonoid (@UpperTheory.Reformulated.B.Re3.L2 n ε)
                (@MeasureTheory.Lp.instAddCommGroup (↥(@UpperTheory.Reformulated.B.Re3.UJ n ε)) Complex
                  (UpperTheory.Reformulated.B.Re3.instMeasurableSpaceUJ n ε)
                  (@OfNat.ofNat ENNReal (nat_lit 2)
                    (@instOfNatAtLeastTwo ENNReal (nat_lit 2)
                      (@AddMonoidWithOne.toNatCast ENNReal
                        (@AddCommMonoidWithOne.toAddMonoidWithOne ENNReal ENNReal.instAddCommMonoidWithOne))
                      UpperTheory.Reformulated.B.Re3.algebra_smulCommClass_complex))
                  (@UpperTheory.Reformulated.B.Re3.muG n ε) Complex.instNormedAddCommGroup))
              (@MeasureTheory.Lp.instModule (↥(@UpperTheory.Reformulated.B.Re3.UJ n ε)) Complex Complex
                (UpperTheory.Reformulated.B.Re3.instMeasurableSpaceUJ n ε)
                (@OfNat.ofNat ENNReal (nat_lit 2)
                  (@instOfNatAtLeastTwo ENNReal (nat_lit 2)
                    (@AddMonoidWithOne.toNatCast ENNReal
                      (@AddCommMonoidWithOne.toAddMonoidWithOne ENNReal ENNReal.instAddCommMonoidWithOne))
                    UpperTheory.Reformulated.B.Re3.algebra_smulCommClass_complex))
                (@UpperTheory.Reformulated.B.Re3.muG n ε) Complex.instNormedAddCommGroup
                (@CStarAlgebra.toNormedRing Complex (@CommCStarAlgebra.toCStarAlgebra Complex instCommCStarAlgebraComplex))
                (@Semiring.toModule Complex
                  (@Ring.toSemiring Complex
                    (@NormedRing.toRing Complex
                      (@CStarAlgebra.toNormedRing Complex
                        (@CommCStarAlgebra.toCStarAlgebra Complex instCommCStarAlgebraComplex)))))
                (@NormedSpace.toIsBoundedSMul Complex Complex Complex.instNormedField
                  (@NonUnitalSeminormedRing.toSeminormedAddCommGroup Complex
                    (@NonUnitalSeminormedCommRing.toNonUnitalSeminormedRing Complex
                      (@SeminormedCommRing.toNonUnitalSeminormedCommRing Complex
                        (@NormedCommRing.toSeminormedCommRing Complex
                          (@CommCStarAlgebra.toNormedCommRing Complex instCommCStarAlgebraComplex)))))
                  (@NonUnitalCStarAlgebra.toNormedSpace Complex
                    (@NonUnitalCommCStarAlgebra.toNonUnitalCStarAlgebra Complex
                      (@CommCStarAlgebra.toNonUnitalCommCStarAlgebra Complex instCommCStarAlgebraComplex)))))},
          (∀ (w : @UpperTheory.Reformulated.B.Re3.L2 n ε),
              @Membership.mem (@UpperTheory.Reformulated.B.Re3.L2 n ε)
                  (@Submodule Complex (@UpperTheory.Reformulated.B.Re3.L2 n ε) Complex.instSemiring
                    (@AddCommGroup.toAddCommMonoid (@UpperTheory.Reformulated.B.Re3.L2 n ε)
                      (@MeasureTheory.Lp.instAddCommGroup (↥(@UpperTheory.Reformulated.B.Re3.UJ n ε)) Complex
                        (UpperTheory.Reformulated.B.Re3.instMeasurableSpaceUJ n ε)
                        (@OfNat.ofNat ENNReal (nat_lit 2)
                          (@instOfNatAtLeastTwo ENNReal (nat_lit 2)
                            (@AddMonoidWithOne.toNatCast ENNReal
                              (@AddCommMonoidWithOne.toAddMonoidWithOne ENNReal ENNReal.instAddCommMonoidWithOne))
                            UpperTheory.Reformulated.B.Re3.algebra_smulCommClass_complex))
                        (@UpperTheory.Reformulated.B.Re3.muG n ε) Complex.instNormedAddCommGroup))
                    (@MeasureTheory.Lp.instModule (↥(@UpperTheory.Reformulated.B.Re3.UJ n ε)) Complex Complex
                      (UpperTheory.Reformulated.B.Re3.instMeasurableSpaceUJ n ε)
                      (@OfNat.ofNat ENNReal (nat_lit 2)
                        (@instOfNatAtLeastTwo ENNReal (nat_lit 2)
                          (@AddMonoidWithOne.toNatCast ENNReal
                            (@AddCommMonoidWithOne.toAddMonoidWithOne ENNReal ENNReal.instAddCommMonoidWithOne))
                          UpperTheory.Reformulated.B.Re3.algebra_smulCommClass_complex))
                      (@UpperTheory.Reformulated.B.Re3.muG n ε) Complex.instNormedAddCommGroup
                      (@CStarAlgebra.toNormedRing Complex
                        (@CommCStarAlgebra.toCStarAlgebra Complex instCommCStarAlgebraComplex))
                      (@Semiring.toModule Complex
                        (@Ring.toSemiring Complex
                          (@NormedRing.toRing Complex
                            (@CStarAlgebra.toNormedRing Complex
                              (@CommCStarAlgebra.toCStarAlgebra Complex instCommCStarAlgebraComplex)))))
                      (@NormedSpace.toIsBoundedSMul Complex Complex Complex.instNormedField
                        (@NonUnitalSeminormedRing.toSeminormedAddCommGroup Complex
                          (@NonUnitalSeminormedCommRing.toNonUnitalSeminormedRing Complex
                            (@SeminormedCommRing.toNonUnitalSeminormedCommRing Complex
                              (@NormedCommRing.toSeminormedCommRing Complex
                                (@CommCStarAlgebra.toNormedCommRing Complex instCommCStarAlgebraComplex)))))
                        (@NonUnitalCStarAlgebra.toNormedSpace Complex
                          (@NonUnitalCommCStarAlgebra.toNonUnitalCStarAlgebra Complex
                            (@CommCStarAlgebra.toNonUnitalCommCStarAlgebra Complex instCommCStarAlgebraComplex))))))
                  (@SetLike.instMembership
                    (@Submodule Complex (@UpperTheory.Reformulated.B.Re3.L2 n ε) Complex.instSemiring
                      (@AddCommGroup.toAddCommMonoid (@UpperTheory.Reformulated.B.Re3.L2 n ε)
                        (@MeasureTheory.Lp.instAddCommGroup (↥(@UpperTheory.Reformulated.B.Re3.UJ n ε)) Complex
                          (UpperTheory.Reformulated.B.Re3.instMeasurableSpaceUJ n ε)
                          (@OfNat.ofNat ENNReal (nat_lit 2)
                            (@instOfNatAtLeastTwo ENNReal (nat_lit 2)
                              (@AddMonoidWithOne.toNatCast ENNReal
                                (@AddCommMonoidWithOne.toAddMonoidWithOne ENNReal ENNReal.instAddCommMonoidWithOne))
                              UpperTheory.Reformulated.B.Re3.algebra_smulCommClass_complex))
                          (@UpperTheory.Reformulated.B.Re3.muG n ε) Complex.instNormedAddCommGroup))
                      (@MeasureTheory.Lp.instModule (↥(@UpperTheory.Reformulated.B.Re3.UJ n ε)) Complex Complex
                        (UpperTheory.Reformulated.B.Re3.instMeasurableSpaceUJ n ε)
                        (@OfNat.ofNat ENNReal (nat_lit 2)
                          (@instOfNatAtLeastTwo ENNReal (nat_lit 2)
                            (@AddMonoidWithOne.toNatCast ENNReal
                              (@AddCommMonoidWithOne.toAddMonoidWithOne ENNReal ENNReal.instAddCommMonoidWithOne))
                            UpperTheory.Reformulated.B.Re3.algebra_smulCommClass_complex))
                        (@UpperTheory.Reformulated.B.Re3.muG n ε) Complex.instNormedAddCommGroup
                        (@CStarAlgebra.toNormedRing Complex
                          (@CommCStarAlgebra.toCStarAlgebra Complex instCommCStarAlgebraComplex))
                        (@Semiring.toModule Complex
                          (@Ring.toSemiring Complex
                            (@NormedRing.toRing Complex
                              (@CStarAlgebra.toNormedRing Complex
                                (@CommCStarAlgebra.toCStarAlgebra Complex instCommCStarAlgebraComplex)))))
                        (@NormedSpace.toIsBoundedSMul Complex Complex Complex.instNormedField
                          (@NonUnitalSeminormedRing.toSeminormedAddCommGroup Complex
                            (@NonUnitalSeminormedCommRing.toNonUnitalSeminormedRing Complex
                              (@SeminormedCommRing.toNonUnitalSeminormedCommRing Complex
                                (@NormedCommRing.toSeminormedCommRing Complex
                                  (@CommCStarAlgebra.toNormedCommRing Complex instCommCStarAlgebraComplex)))))
                          (@NonUnitalCStarAlgebra.toNormedSpace Complex
                            (@NonUnitalCommCStarAlgebra.toNonUnitalCStarAlgebra Complex
                              (@CommCStarAlgebra.toNonUnitalCommCStarAlgebra Complex instCommCStarAlgebraComplex))))))
                    (@UpperTheory.Reformulated.B.Re3.L2 n ε)
                    (@Submodule.setLike Complex (@UpperTheory.Reformulated.B.Re3.L2 n ε) Complex.instSemiring
                      (@AddCommGroup.toAddCommMonoid (@UpperTheory.Reformulated.B.Re3.L2 n ε)
                        (@MeasureTheory.Lp.instAddCommGroup (↥(@UpperTheory.Reformulated.B.Re3.UJ n ε)) Complex
                          (UpperTheory.Reformulated.B.Re3.instMeasurableSpaceUJ n ε)
                          (@OfNat.ofNat ENNReal (nat_lit 2)
                            (@instOfNatAtLeastTwo ENNReal (nat_lit 2)
                              (@AddMonoidWithOne.toNatCast ENNReal
                                (@AddCommMonoidWithOne.toAddMonoidWithOne ENNReal ENNReal.instAddCommMonoidWithOne))
                              UpperTheory.Reformulated.B.Re3.algebra_smulCommClass_complex))
                          (@UpperTheory.Reformulated.B.Re3.muG n ε) Complex.instNormedAddCommGroup))
                      (@MeasureTheory.Lp.instModule (↥(@UpperTheory.Reformulated.B.Re3.UJ n ε)) Complex Complex
                        (UpperTheory.Reformulated.B.Re3.instMeasurableSpaceUJ n ε)
                        (@OfNat.ofNat ENNReal (nat_lit 2)
                          (@instOfNatAtLeastTwo ENNReal (nat_lit 2)
                            (@AddMonoidWithOne.toNatCast ENNReal
                              (@AddCommMonoidWithOne.toAddMonoidWithOne ENNReal ENNReal.instAddCommMonoidWithOne))
                            UpperTheory.Reformulated.B.Re3.algebra_smulCommClass_complex))
                        (@UpperTheory.Reformulated.B.Re3.muG n ε) Complex.instNormedAddCommGroup
                        (@CStarAlgebra.toNormedRing Complex
                          (@CommCStarAlgebra.toCStarAlgebra Complex instCommCStarAlgebraComplex))
                        (@Semiring.toModule Complex
                          (@Ring.toSemiring Complex
                            (@NormedRing.toRing Complex
                              (@CStarAlgebra.toNormedRing Complex
                                (@CommCStarAlgebra.toCStarAlgebra Complex instCommCStarAlgebraComplex)))))
                        (@NormedSpace.toIsBoundedSMul Complex Complex Complex.instNormedField
                          (@NonUnitalSeminormedRing.toSeminormedAddCommGroup Complex
                            (@NonUnitalSeminormedCommRing.toNonUnitalSeminormedRing Complex
                              (@SeminormedCommRing.toNonUnitalSeminormedCommRing Complex
                                (@NormedCommRing.toSeminormedCommRing Complex
                                  (@CommCStarAlgebra.toNormedCommRing Complex instCommCStarAlgebraComplex)))))
                          (@NonUnitalCStarAlgebra.toNormedSpace Complex
                            (@NonUnitalCommCStarAlgebra.toNonUnitalCStarAlgebra Complex
                              (@CommCStarAlgebra.toNonUnitalCommCStarAlgebra Complex instCommCStarAlgebraComplex)))))))
                  S w →
                @Eq (@UpperTheory.Reformulated.B.Re3.L2 n ε)
                    (@DFunLike.coe
                      (@LinearMap Complex Complex Complex.instSemiring Complex.instSemiring
                        (@RingHom.id Complex (@Semiring.toNonAssocSemiring Complex Complex.instSemiring))
                        (@UpperTheory.Reformulated.B.Re3.L2 n ε) (@UpperTheory.Reformulated.B.Re3.L2 n ε)
                        (@AddCommGroup.toAddCommMonoid (@UpperTheory.Reformulated.B.Re3.L2 n ε)
                          (@MeasureTheory.Lp.instAddCommGroup (↥(@UpperTheory.Reformulated.B.Re3.UJ n ε)) Complex
                            (UpperTheory.Reformulated.B.Re3.instMeasurableSpaceUJ n ε)
                            (@OfNat.ofNat ENNReal (nat_lit 2)
                              (@instOfNatAtLeastTwo ENNReal (nat_lit 2)
                                (@AddMonoidWithOne.toNatCast ENNReal
                                  (@AddCommMonoidWithOne.toAddMonoidWithOne ENNReal ENNReal.instAddCommMonoidWithOne))
                                UpperTheory.Reformulated.B.Re3.algebra_smulCommClass_complex))
                            (@UpperTheory.Reformulated.B.Re3.muG n ε) Complex.instNormedAddCommGroup))
                        (@AddCommGroup.toAddCommMonoid (@UpperTheory.Reformulated.B.Re3.L2 n ε)
                          (@MeasureTheory.Lp.instAddCommGroup (↥(@UpperTheory.Reformulated.B.Re3.UJ n ε)) Complex
                            (UpperTheory.Reformulated.B.Re3.instMeasurableSpaceUJ n ε)
                            (@OfNat.ofNat ENNReal (nat_lit 2)
                              (@instOfNatAtLeastTwo ENNReal (nat_lit 2)
                                (@AddMonoidWithOne.toNatCast ENNReal
                                  (@AddCommMonoidWithOne.toAddMonoidWithOne ENNReal ENNReal.instAddCommMonoidWithOne))
                                UpperTheory.Reformulated.B.Re3.algebra_smulCommClass_complex))
                            (@UpperTheory.Reformulated.B.Re3.muG n ε) Complex.instNormedAddCommGroup))
                        (@MeasureTheory.Lp.instModule (↥(@UpperTheory.Reformulated.B.Re3.UJ n ε)) Complex Complex
                          (UpperTheory.Reformulated.B.Re3.instMeasurableSpaceUJ n ε)
                          (@OfNat.ofNat ENNReal (nat_lit 2)
                            (@instOfNatAtLeastTwo ENNReal (nat_lit 2)
                              (@AddMonoidWithOne.toNatCast ENNReal
                                (@AddCommMonoidWithOne.toAddMonoidWithOne ENNReal ENNReal.instAddCommMonoidWithOne))
                              UpperTheory.Reformulated.B.Re3.algebra_smulCommClass_complex))
                          (@UpperTheory.Reformulated.B.Re3.muG n ε) Complex.instNormedAddCommGroup
                          (@CStarAlgebra.toNormedRing Complex
                            (@CommCStarAlgebra.toCStarAlgebra Complex instCommCStarAlgebraComplex))
                          (@Semiring.toModule Complex
                            (@Ring.toSemiring Complex
                              (@NormedRing.toRing Complex
                                (@CStarAlgebra.toNormedRing Complex
                                  (@CommCStarAlgebra.toCStarAlgebra Complex instCommCStarAlgebraComplex)))))
                          (@NormedSpace.toIsBoundedSMul Complex Complex Complex.instNormedField
                            (@NonUnitalSeminormedRing.toSeminormedAddCommGroup Complex
                              (@NonUnitalSeminormedCommRing.toNonUnitalSeminormedRing Complex
                                (@SeminormedCommRing.toNonUnitalSeminormedCommRing Complex
                                  (@NormedCommRing.toSeminormedCommRing Complex
                                    (@CommCStarAlgebra.toNormedCommRing Complex instCommCStarAlgebraComplex)))))
                            (@NonUnitalCStarAlgebra.toNormedSpace Complex
                              (@NonUnitalCommCStarAlgebra.toNonUnitalCStarAlgebra Complex
                                (@CommCStarAlgebra.toNonUnitalCommCStarAlgebra Complex instCommCStarAlgebraComplex)))))
                        (@MeasureTheory.Lp.instModule (↥(@UpperTheory.Reformulated.B.Re3.UJ n ε)) Complex Complex
                          (UpperTheory.Reformulated.B.Re3.instMeasurableSpaceUJ n ε)
                          (@OfNat.ofNat ENNReal (nat_lit 2)
                            (@instOfNatAtLeastTwo ENNReal (nat_lit 2)
                              (@AddMonoidWithOne.toNatCast ENNReal
                                (@AddCommMonoidWithOne.toAddMonoidWithOne ENNReal ENNReal.instAddCommMonoidWithOne))
                              UpperTheory.Reformulated.B.Re3.algebra_smulCommClass_complex))
                          (@UpperTheory.Reformulated.B.Re3.muG n ε) Complex.instNormedAddCommGroup
                          (@CStarAlgebra.toNormedRing Complex
                            (@CommCStarAlgebra.toCStarAlgebra Complex instCommCStarAlgebraComplex))
                          (@Semiring.toModule Complex
                            (@Ring.toSemiring Complex
                              (@NormedRing.toRing Complex
                                (@CStarAlgebra.toNormedRing Complex
                                  (@CommCStarAlgebra.toCStarAlgebra Complex instCommCStarAlgebraComplex)))))
                          (@NormedSpace.toIsBoundedSMul Complex Complex Complex.instNormedField
                            (@NonUnitalSeminormedRing.toSeminormedAddCommGroup Complex
                              (@NonUnitalSeminormedCommRing.toNonUnitalSeminormedRing Complex
                                (@SeminormedCommRing.toNonUnitalSeminormedCommRing Complex
                                  (@NormedCommRing.toSeminormedCommRing Complex
                                    (@CommCStarAlgebra.toNormedCommRing Complex instCommCStarAlgebraComplex)))))
                            (@NonUnitalCStarAlgebra.toNormedSpace Complex
                              (@NonUnitalCommCStarAlgebra.toNonUnitalCStarAlgebra Complex
                                (@CommCStarAlgebra.toNonUnitalCommCStarAlgebra Complex instCommCStarAlgebraComplex))))))
                      (@UpperTheory.Reformulated.B.Re3.L2 n ε) (fun (x : @UpperTheory.Reformulated.B.Re3.L2 n ε) ↦ @UpperTheory.Reformulated.B.Re3.L2 n ε)
                      (@LinearMap.instFunLike Complex Complex (@UpperTheory.Reformulated.B.Re3.L2 n ε) (@UpperTheory.Reformulated.B.Re3.L2 n ε)
                        Complex.instSemiring Complex.instSemiring
                        (@AddCommGroup.toAddCommMonoid (@UpperTheory.Reformulated.B.Re3.L2 n ε)
                          (@MeasureTheory.Lp.instAddCommGroup (↥(@UpperTheory.Reformulated.B.Re3.UJ n ε)) Complex
                            (UpperTheory.Reformulated.B.Re3.instMeasurableSpaceUJ n ε)
                            (@OfNat.ofNat ENNReal (nat_lit 2)
                              (@instOfNatAtLeastTwo ENNReal (nat_lit 2)
                                (@AddMonoidWithOne.toNatCast ENNReal
                                  (@AddCommMonoidWithOne.toAddMonoidWithOne ENNReal ENNReal.instAddCommMonoidWithOne))
                                UpperTheory.Reformulated.B.Re3.algebra_smulCommClass_complex))
                            (@UpperTheory.Reformulated.B.Re3.muG n ε) Complex.instNormedAddCommGroup))
                        (@AddCommGroup.toAddCommMonoid (@UpperTheory.Reformulated.B.Re3.L2 n ε)
                          (@MeasureTheory.Lp.instAddCommGroup (↥(@UpperTheory.Reformulated.B.Re3.UJ n ε)) Complex
                            (UpperTheory.Reformulated.B.Re3.instMeasurableSpaceUJ n ε)
                            (@OfNat.ofNat ENNReal (nat_lit 2)
                              (@instOfNatAtLeastTwo ENNReal (nat_lit 2)
                                (@AddMonoidWithOne.toNatCast ENNReal
                                  (@AddCommMonoidWithOne.toAddMonoidWithOne ENNReal ENNReal.instAddCommMonoidWithOne))
                                UpperTheory.Reformulated.B.Re3.algebra_smulCommClass_complex))
                            (@UpperTheory.Reformulated.B.Re3.muG n ε) Complex.instNormedAddCommGroup))
                        (@MeasureTheory.Lp.instModule (↥(@UpperTheory.Reformulated.B.Re3.UJ n ε)) Complex Complex
                          (UpperTheory.Reformulated.B.Re3.instMeasurableSpaceUJ n ε)
                          (@OfNat.ofNat ENNReal (nat_lit 2)
                            (@instOfNatAtLeastTwo ENNReal (nat_lit 2)
                              (@AddMonoidWithOne.toNatCast ENNReal
                                (@AddCommMonoidWithOne.toAddMonoidWithOne ENNReal ENNReal.instAddCommMonoidWithOne))
                              UpperTheory.Reformulated.B.Re3.algebra_smulCommClass_complex))
                          (@UpperTheory.Reformulated.B.Re3.muG n ε) Complex.instNormedAddCommGroup
                          (@CStarAlgebra.toNormedRing Complex
                            (@CommCStarAlgebra.toCStarAlgebra Complex instCommCStarAlgebraComplex))
                          (@Semiring.toModule Complex
                            (@Ring.toSemiring Complex
                              (@NormedRing.toRing Complex
                                (@CStarAlgebra.toNormedRing Complex
                                  (@CommCStarAlgebra.toCStarAlgebra Complex instCommCStarAlgebraComplex)))))
                          (@NormedSpace.toIsBoundedSMul Complex Complex Complex.instNormedField
                            (@NonUnitalSeminormedRing.toSeminormedAddCommGroup Complex
                              (@NonUnitalSeminormedCommRing.toNonUnitalSeminormedRing Complex
                                (@SeminormedCommRing.toNonUnitalSeminormedCommRing Complex
                                  (@NormedCommRing.toSeminormedCommRing Complex
                                    (@CommCStarAlgebra.toNormedCommRing Complex instCommCStarAlgebraComplex)))))
                            (@NonUnitalCStarAlgebra.toNormedSpace Complex
                              (@NonUnitalCommCStarAlgebra.toNonUnitalCStarAlgebra Complex
                                (@CommCStarAlgebra.toNonUnitalCommCStarAlgebra Complex instCommCStarAlgebraComplex)))))
                        (@MeasureTheory.Lp.instModule (↥(@UpperTheory.Reformulated.B.Re3.UJ n ε)) Complex Complex
                          (UpperTheory.Reformulated.B.Re3.instMeasurableSpaceUJ n ε)
                          (@OfNat.ofNat ENNReal (nat_lit 2)
                            (@instOfNatAtLeastTwo ENNReal (nat_lit 2)
                              (@AddMonoidWithOne.toNatCast ENNReal
                                (@AddCommMonoidWithOne.toAddMonoidWithOne ENNReal ENNReal.instAddCommMonoidWithOne))
                              UpperTheory.Reformulated.B.Re3.algebra_smulCommClass_complex))
                          (@UpperTheory.Reformulated.B.Re3.muG n ε) Complex.instNormedAddCommGroup
                          (@CStarAlgebra.toNormedRing Complex
                            (@CommCStarAlgebra.toCStarAlgebra Complex instCommCStarAlgebraComplex))
                          (@Semiring.toModule Complex
                            (@Ring.toSemiring Complex
                              (@NormedRing.toRing Complex
                                (@CStarAlgebra.toNormedRing Complex
                                  (@CommCStarAlgebra.toCStarAlgebra Complex instCommCStarAlgebraComplex)))))
                          (@NormedSpace.toIsBoundedSMul Complex Complex Complex.instNormedField
                            (@NonUnitalSeminormedRing.toSeminormedAddCommGroup Complex
                              (@NonUnitalSeminormedCommRing.toNonUnitalSeminormedRing Complex
                                (@SeminormedCommRing.toNonUnitalSeminormedCommRing Complex
                                  (@NormedCommRing.toSeminormedCommRing Complex
                                    (@CommCStarAlgebra.toNormedCommRing Complex instCommCStarAlgebraComplex)))))
                            (@NonUnitalCStarAlgebra.toNormedSpace Complex
                              (@NonUnitalCommCStarAlgebra.toNonUnitalCStarAlgebra Complex
                                (@CommCStarAlgebra.toNonUnitalCommCStarAlgebra Complex instCommCStarAlgebraComplex)))))
                        (@RingHom.id Complex (@Semiring.toNonAssocSemiring Complex Complex.instSemiring)))
                      A w)
                    (@OfNat.ofNat (@UpperTheory.Reformulated.B.Re3.L2 n ε) (nat_lit 0)
                      (@Zero.toOfNat0 (@UpperTheory.Reformulated.B.Re3.L2 n ε)
                        (@AddSubgroup.zero
                          (@MeasureTheory.AEEqFun (↥(@UpperTheory.Reformulated.B.Re3.UJ n ε)) Complex
                            (UpperTheory.Reformulated.B.Re3.instMeasurableSpaceUJ n ε)
                            (@UniformSpace.toTopologicalSpace Complex
                              (@PseudoMetricSpace.toUniformSpace Complex
                                (@SeminormedAddCommGroup.toPseudoMetricSpace Complex
                                  (@NormedAddCommGroup.toSeminormedAddCommGroup Complex Complex.instNormedAddCommGroup))))
                            (@UpperTheory.Reformulated.B.Re3.muG n ε))
                          (@MeasureTheory.AEEqFun.instAddGroup (↥(@UpperTheory.Reformulated.B.Re3.UJ n ε)) Complex
                            (UpperTheory.Reformulated.B.Re3.instMeasurableSpaceUJ n ε) (@UpperTheory.Reformulated.B.Re3.muG n ε)
                            (@UniformSpace.toTopologicalSpace Complex
                              (@PseudoMetricSpace.toUniformSpace Complex
                                (@SeminormedAddCommGroup.toPseudoMetricSpace Complex
                                  (@NormedAddCommGroup.toSeminormedAddCommGroup Complex Complex.instNormedAddCommGroup))))
                            (@AddCommGroup.toAddGroup Complex
                              (@NormedAddCommGroup.toAddCommGroup Complex Complex.instNormedAddCommGroup))
                            (@SeminormedAddCommGroup.toIsTopologicalAddGroup Complex
                              (@NormedAddCommGroup.toSeminormedAddCommGroup Complex Complex.instNormedAddCommGroup)))
                          (@MeasureTheory.Lp (↥(@UpperTheory.Reformulated.B.Re3.UJ n ε)) Complex
                            (UpperTheory.Reformulated.B.Re3.instMeasurableSpaceUJ n ε) Complex.instNormedAddCommGroup
                            (@OfNat.ofNat ENNReal (nat_lit 2)
                              (@instOfNatAtLeastTwo ENNReal (nat_lit 2)
                                (@AddMonoidWithOne.toNatCast ENNReal
                                  (@AddCommMonoidWithOne.toAddMonoidWithOne ENNReal ENNReal.instAddCommMonoidWithOne))
                                UpperTheory.Reformulated.B.Re3.algebra_smulCommClass_complex))
                            (@UpperTheory.Reformulated.B.Re3.muG n ε))))) →
                  @Eq (@UpperTheory.Reformulated.B.Re3.L2 n ε) w
                    (@OfNat.ofNat (@UpperTheory.Reformulated.B.Re3.L2 n ε) (nat_lit 0)
                      (@Zero.toOfNat0 (@UpperTheory.Reformulated.B.Re3.L2 n ε)
                        (@AddSubgroup.zero
                          (@MeasureTheory.AEEqFun (↥(@UpperTheory.Reformulated.B.Re3.UJ n ε)) Complex
                            (UpperTheory.Reformulated.B.Re3.instMeasurableSpaceUJ n ε)
                            (@UniformSpace.toTopologicalSpace Complex
                              (@PseudoMetricSpace.toUniformSpace Complex
                                (@SeminormedAddCommGroup.toPseudoMetricSpace Complex
                                  (@NormedAddCommGroup.toSeminormedAddCommGroup Complex Complex.instNormedAddCommGroup))))
                            (@UpperTheory.Reformulated.B.Re3.muG n ε))
                          (@MeasureTheory.AEEqFun.instAddGroup (↥(@UpperTheory.Reformulated.B.Re3.UJ n ε)) Complex
                            (UpperTheory.Reformulated.B.Re3.instMeasurableSpaceUJ n ε) (@UpperTheory.Reformulated.B.Re3.muG n ε)
                            (@UniformSpace.toTopologicalSpace Complex
                              (@PseudoMetricSpace.toUniformSpace Complex
                                (@SeminormedAddCommGroup.toPseudoMetricSpace Complex
                                  (@NormedAddCommGroup.toSeminormedAddCommGroup Complex Complex.instNormedAddCommGroup))))
                            (@AddCommGroup.toAddGroup Complex
                              (@NormedAddCommGroup.toAddCommGroup Complex Complex.instNormedAddCommGroup))
                            (@SeminormedAddCommGroup.toIsTopologicalAddGroup Complex
                              (@NormedAddCommGroup.toSeminormedAddCommGroup Complex Complex.instNormedAddCommGroup)))
                          (@MeasureTheory.Lp (↥(@UpperTheory.Reformulated.B.Re3.UJ n ε)) Complex
                            (UpperTheory.Reformulated.B.Re3.instMeasurableSpaceUJ n ε) Complex.instNormedAddCommGroup
                            (@OfNat.ofNat ENNReal (nat_lit 2)
                              (@instOfNatAtLeastTwo ENNReal (nat_lit 2)
                                (@AddMonoidWithOne.toNatCast ENNReal
                                  (@AddCommMonoidWithOne.toAddMonoidWithOne ENNReal ENNReal.instAddCommMonoidWithOne))
                                UpperTheory.Reformulated.B.Re3.algebra_smulCommClass_complex))
                            (@UpperTheory.Reformulated.B.Re3.muG n ε)))))) →
            @UpperTheory.Reformulated.B.Re3.IsKTypeOf n (@UpperTheory.Reformulated.B.Re3.L2 n ε)
                (@MeasureTheory.Lp.instNormedAddCommGroup (↥(@UpperTheory.Reformulated.B.Re3.UJ n ε)) Complex
                  (UpperTheory.Reformulated.B.Re3.instMeasurableSpaceUJ n ε)
                  (@OfNat.ofNat ENNReal (nat_lit 2)
                    (@instOfNatAtLeastTwo ENNReal (nat_lit 2)
                      (@AddMonoidWithOne.toNatCast ENNReal
                        (@AddCommMonoidWithOne.toAddMonoidWithOne ENNReal ENNReal.instAddCommMonoidWithOne))
                      UpperTheory.Reformulated.B.Re3.algebra_smulCommClass_complex))
                  (@UpperTheory.Reformulated.B.Re3.muG n ε) Complex.instNormedAddCommGroup fact_one_le_two_ennreal)
                (@MeasureTheory.L2.innerProductSpace (↥(@UpperTheory.Reformulated.B.Re3.UJ n ε)) Complex Complex Complex.instRCLike
                  (UpperTheory.Reformulated.B.Re3.instMeasurableSpaceUJ n ε) (@UpperTheory.Reformulated.B.Re3.muG n ε) Complex.instNormedAddCommGroup
                  (@RCLike.innerProductSpace Complex Complex.instRCLike))
                ε (@UpperTheory.Reformulated.B.Re3.rreg n ε) Λ S →
              @UpperTheory.Reformulated.B.Re3.IsKTypeOf n (@UpperTheory.Reformulated.B.Re3.L2 n ε)
                (@MeasureTheory.Lp.instNormedAddCommGroup (↥(@UpperTheory.Reformulated.B.Re3.UJ n ε)) Complex
                  (UpperTheory.Reformulated.B.Re3.instMeasurableSpaceUJ n ε)
                  (@OfNat.ofNat ENNReal (nat_lit 2)
                    (@instOfNatAtLeastTwo ENNReal (nat_lit 2)
                      (@AddMonoidWithOne.toNatCast ENNReal
                        (@AddCommMonoidWithOne.toAddMonoidWithOne ENNReal ENNReal.instAddCommMonoidWithOne))
                      UpperTheory.Reformulated.B.Re3.algebra_smulCommClass_complex))
                  (@UpperTheory.Reformulated.B.Re3.muG n ε) Complex.instNormedAddCommGroup fact_one_le_two_ennreal)
                (@MeasureTheory.L2.innerProductSpace (↥(@UpperTheory.Reformulated.B.Re3.UJ n ε)) Complex Complex Complex.instRCLike
                  (UpperTheory.Reformulated.B.Re3.instMeasurableSpaceUJ n ε) (@UpperTheory.Reformulated.B.Re3.muG n ε) Complex.instNormedAddCommGroup
                  (@RCLike.innerProductSpace Complex Complex.instRCLike))
                ε (@UpperTheory.Reformulated.B.Re3.rreg n ε) Λ
                (@Submodule.map Complex Complex (@UpperTheory.Reformulated.B.Re3.L2 n ε) (@UpperTheory.Reformulated.B.Re3.L2 n ε) Complex.instSemiring
                  Complex.instSemiring
                  (@AddCommGroup.toAddCommMonoid (@UpperTheory.Reformulated.B.Re3.L2 n ε)
                    (@MeasureTheory.Lp.instAddCommGroup (↥(@UpperTheory.Reformulated.B.Re3.UJ n ε)) Complex
                      (UpperTheory.Reformulated.B.Re3.instMeasurableSpaceUJ n ε)
                      (@OfNat.ofNat ENNReal (nat_lit 2)
                        (@instOfNatAtLeastTwo ENNReal (nat_lit 2)
                          (@AddMonoidWithOne.toNatCast ENNReal
                            (@AddCommMonoidWithOne.toAddMonoidWithOne ENNReal ENNReal.instAddCommMonoidWithOne))
                          UpperTheory.Reformulated.B.Re3.algebra_smulCommClass_complex))
                      (@UpperTheory.Reformulated.B.Re3.muG n ε) Complex.instNormedAddCommGroup))
                  (@AddCommGroup.toAddCommMonoid (@UpperTheory.Reformulated.B.Re3.L2 n ε)
                    (@NormedAddCommGroup.toAddCommGroup (@UpperTheory.Reformulated.B.Re3.L2 n ε)
                      (@MeasureTheory.Lp.instNormedAddCommGroup (↥(@UpperTheory.Reformulated.B.Re3.UJ n ε)) Complex
                        (UpperTheory.Reformulated.B.Re3.instMeasurableSpaceUJ n ε)
                        (@OfNat.ofNat ENNReal (nat_lit 2)
                          (@instOfNatAtLeastTwo ENNReal (nat_lit 2)
                            (@AddMonoidWithOne.toNatCast ENNReal
                              (@AddCommMonoidWithOne.toAddMonoidWithOne ENNReal ENNReal.instAddCommMonoidWithOne))
                            UpperTheory.Reformulated.B.Re3.algebra_smulCommClass_complex))
                        (@UpperTheory.Reformulated.B.Re3.muG n ε) Complex.instNormedAddCommGroup fact_one_le_two_ennreal)))
                  (@MeasureTheory.Lp.instModule (↥(@UpperTheory.Reformulated.B.Re3.UJ n ε)) Complex Complex
                    (UpperTheory.Reformulated.B.Re3.instMeasurableSpaceUJ n ε)
                    (@OfNat.ofNat ENNReal (nat_lit 2)
                      (@instOfNatAtLeastTwo ENNReal (nat_lit 2)
                        (@AddMonoidWithOne.toNatCast ENNReal
                          (@AddCommMonoidWithOne.toAddMonoidWithOne ENNReal ENNReal.instAddCommMonoidWithOne))
                        UpperTheory.Reformulated.B.Re3.algebra_smulCommClass_complex))
                    (@UpperTheory.Reformulated.B.Re3.muG n ε) Complex.instNormedAddCommGroup
                    (@CStarAlgebra.toNormedRing Complex
                      (@CommCStarAlgebra.toCStarAlgebra Complex instCommCStarAlgebraComplex))
                    (@Semiring.toModule Complex
                      (@Ring.toSemiring Complex
                        (@NormedRing.toRing Complex
                          (@CStarAlgebra.toNormedRing Complex
                            (@CommCStarAlgebra.toCStarAlgebra Complex instCommCStarAlgebraComplex)))))
                    (@NormedSpace.toIsBoundedSMul Complex Complex Complex.instNormedField
                      (@NonUnitalSeminormedRing.toSeminormedAddCommGroup Complex
                        (@NonUnitalSeminormedCommRing.toNonUnitalSeminormedRing Complex
                          (@SeminormedCommRing.toNonUnitalSeminormedCommRing Complex
                            (@NormedCommRing.toSeminormedCommRing Complex
                              (@CommCStarAlgebra.toNormedCommRing Complex instCommCStarAlgebraComplex)))))
                      (@NonUnitalCStarAlgebra.toNormedSpace Complex
                        (@NonUnitalCommCStarAlgebra.toNonUnitalCStarAlgebra Complex
                          (@CommCStarAlgebra.toNonUnitalCommCStarAlgebra Complex instCommCStarAlgebraComplex)))))
                  (@NormedSpace.toModule Complex (@UpperTheory.Reformulated.B.Re3.L2 n ε) Complex.instNormedField
                    (@NormedAddCommGroup.toSeminormedAddCommGroup (@UpperTheory.Reformulated.B.Re3.L2 n ε)
                      (@MeasureTheory.Lp.instNormedAddCommGroup (↥(@UpperTheory.Reformulated.B.Re3.UJ n ε)) Complex
                        (UpperTheory.Reformulated.B.Re3.instMeasurableSpaceUJ n ε)
                        (@OfNat.ofNat ENNReal (nat_lit 2)
                          (@instOfNatAtLeastTwo ENNReal (nat_lit 2)
                            (@AddMonoidWithOne.toNatCast ENNReal
                              (@AddCommMonoidWithOne.toAddMonoidWithOne ENNReal ENNReal.instAddCommMonoidWithOne))
                            UpperTheory.Reformulated.B.Re3.algebra_smulCommClass_complex))
                        (@UpperTheory.Reformulated.B.Re3.muG n ε) Complex.instNormedAddCommGroup fact_one_le_two_ennreal))
                    (@InnerProductSpace.toNormedSpace Complex (@UpperTheory.Reformulated.B.Re3.L2 n ε) Complex.instRCLike
                      (@NormedAddCommGroup.toSeminormedAddCommGroup (@UpperTheory.Reformulated.B.Re3.L2 n ε)
                        (@MeasureTheory.Lp.instNormedAddCommGroup (↥(@UpperTheory.Reformulated.B.Re3.UJ n ε)) Complex
                          (UpperTheory.Reformulated.B.Re3.instMeasurableSpaceUJ n ε)
                          (@OfNat.ofNat ENNReal (nat_lit 2)
                            (@instOfNatAtLeastTwo ENNReal (nat_lit 2)
                              (@AddMonoidWithOne.toNatCast ENNReal
                                (@AddCommMonoidWithOne.toAddMonoidWithOne ENNReal ENNReal.instAddCommMonoidWithOne))
                              UpperTheory.Reformulated.B.Re3.algebra_smulCommClass_complex))
                          (@UpperTheory.Reformulated.B.Re3.muG n ε) Complex.instNormedAddCommGroup fact_one_le_two_ennreal))
                      (@MeasureTheory.L2.innerProductSpace (↥(@UpperTheory.Reformulated.B.Re3.UJ n ε)) Complex Complex Complex.instRCLike
                        (UpperTheory.Reformulated.B.Re3.instMeasurableSpaceUJ n ε) (@UpperTheory.Reformulated.B.Re3.muG n ε)
                        Complex.instNormedAddCommGroup (@RCLike.innerProductSpace Complex Complex.instRCLike))))
                  (@RingHom.id Complex (@Semiring.toNonAssocSemiring Complex Complex.instSemiring))
                  (@RingHomSurjective.ids Complex Complex.instSemiring) A S) := by sorry
