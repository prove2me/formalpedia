-- Prove2me | Theorems.Thm_UpperTheory_Reformulated_B_SelectionLemmas_main
-- name    : UpperTheory.Reformulated.B.SelectionLemmas.main
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-22T23:19:41.323806+00:00
-- url     : https://prove2.me/theorems/cb30fc62-7008-49a5-bb22-fb631f75b8f6
-- title:
--   Selection Lemmas: main
-- statement:
--   The Selection Lemmas construction uses the main property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicArithmetic/IntegralCasts/CapelliIdentities/SelectionLemmas.lean#L3135-L3547
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicArithmetic/IntegralCasts/CapelliIdentities/SelectionLemmas.lean#L3135-L3547

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

theorem UpperTheory.Reformulated.B.SelectionLemmas.main :
    ∀ {K : Type} [inst : Field K] [inst_1 : @NumberField K inst]
      [inst_2 :
        @StarRing K
          (@NonUnitalNonAssocRing.toNonUnitalNonAssocSemiring K
            (@NonUnitalNonAssocCommRing.toNonUnitalNonAssocRing K
              (@NonUnitalCommRing.toNonUnitalNonAssocCommRing K
                (@CommRing.toNonUnitalCommRing K (@Field.toCommRing K inst)))))]
      {n D : Nat} (H : Matrix (Fin n) (Fin n) K) (P : Matrix (Fin D) (Fin n) K)
      (M :
        @Submodule (@NumberField.RingOfIntegers K inst) (Fin n → K)
          (@CommSemiring.toSemiring (@NumberField.RingOfIntegers K inst)
            (@CommRing.toCommSemiring (@NumberField.RingOfIntegers K inst)
              (@NumberField.instCommRingRingOfIntegers K inst)))
          (@Pi.addCommMonoid (Fin n) (fun (a : Fin n) ↦ K) fun (i : Fin n) ↦
            @Semiring.toAddCommMonoid K
              (@DivisionSemiring.toSemiring K (@Semifield.toDivisionSemiring K (@Field.toSemifield K inst))))
          (@Pi.Function.module (Fin n) (@NumberField.RingOfIntegers K inst) K
            (@CommSemiring.toSemiring (@NumberField.RingOfIntegers K inst)
              (@CommRing.toCommSemiring (@NumberField.RingOfIntegers K inst)
                (@NumberField.instCommRingRingOfIntegers K inst)))
            (@Semiring.toAddCommMonoid K
              (@DivisionSemiring.toSemiring K (@Semifield.toDivisionSemiring K (@Field.toSemifield K inst))))
            (@Algebra.toModule (@NumberField.RingOfIntegers K inst) K
              (@CommRing.toCommSemiring (@NumberField.RingOfIntegers K inst)
                (@NumberField.instCommRingRingOfIntegers K inst))
              (@DivisionSemiring.toSemiring K (@Semifield.toDivisionSemiring K (@Field.toSemifield K inst)))
              (@NumberField.RingOfIntegers.instAlgebra_1 K inst)))),
      @Submodule.FG (@NumberField.RingOfIntegers K inst) (Fin n → K)
          (@CommSemiring.toSemiring (@NumberField.RingOfIntegers K inst)
            (@CommRing.toCommSemiring (@NumberField.RingOfIntegers K inst)
              (@NumberField.instCommRingRingOfIntegers K inst)))
          (@Pi.addCommMonoid (Fin n) (fun (a : Fin n) ↦ K) fun (i : Fin n) ↦
            @Semiring.toAddCommMonoid K
              (@DivisionSemiring.toSemiring K (@Semifield.toDivisionSemiring K (@Field.toSemifield K inst))))
          (@Pi.Function.module (Fin n) (@NumberField.RingOfIntegers K inst) K
            (@CommSemiring.toSemiring (@NumberField.RingOfIntegers K inst)
              (@CommRing.toCommSemiring (@NumberField.RingOfIntegers K inst)
                (@NumberField.instCommRingRingOfIntegers K inst)))
            (@Semiring.toAddCommMonoid K
              (@DivisionSemiring.toSemiring K (@Semifield.toDivisionSemiring K (@Field.toSemifield K inst))))
            (@Algebra.toModule (@NumberField.RingOfIntegers K inst) K
              (@CommRing.toCommSemiring (@NumberField.RingOfIntegers K inst)
                (@NumberField.instCommRingRingOfIntegers K inst))
              (@DivisionSemiring.toSemiring K (@Semifield.toDivisionSemiring K (@Field.toSemifield K inst)))
              (@NumberField.RingOfIntegers.instAlgebra_1 K inst)))
          M →
        ∀ (l g : Nat),
          @LT.lt Nat instLTNat (@OfNat.ofNat Nat (nat_lit 0) (instOfNatNat (nat_lit 0))) l →
            (∀ (x : Fin n → K),
                @Membership.mem (Fin n → K)
                    (@Submodule (@NumberField.RingOfIntegers K inst) (Fin n → K)
                      (@CommSemiring.toSemiring (@NumberField.RingOfIntegers K inst)
                        (@CommRing.toCommSemiring (@NumberField.RingOfIntegers K inst)
                          (@NumberField.instCommRingRingOfIntegers K inst)))
                      (@AddCommGroup.toAddCommMonoid (Fin n → K)
                        (@Pi.addCommGroup (Fin n) (fun (a : Fin n) ↦ K) fun (i : Fin n) ↦
                          @Ring.toAddCommGroup K (@DivisionRing.toRing K (@Field.toDivisionRing K inst))))
                      (@Pi.Function.module (Fin n) (@NumberField.RingOfIntegers K inst) K
                        (@CommSemiring.toSemiring (@NumberField.RingOfIntegers K inst)
                          (@CommRing.toCommSemiring (@NumberField.RingOfIntegers K inst)
                            (@NumberField.instCommRingRingOfIntegers K inst)))
                        (@Semiring.toAddCommMonoid K
                          (@DivisionSemiring.toSemiring K (@Semifield.toDivisionSemiring K (@Field.toSemifield K inst))))
                        (@Algebra.toModule (@NumberField.RingOfIntegers K inst) K
                          (@CommRing.toCommSemiring (@NumberField.RingOfIntegers K inst)
                            (@NumberField.instCommRingRingOfIntegers K inst))
                          (@DivisionSemiring.toSemiring K (@Semifield.toDivisionSemiring K (@Field.toSemifield K inst)))
                          (@NumberField.RingOfIntegers.instAlgebra_1 K inst))))
                    (@SetLike.instMembership
                      (@Submodule (@NumberField.RingOfIntegers K inst) (Fin n → K)
                        (@CommSemiring.toSemiring (@NumberField.RingOfIntegers K inst)
                          (@CommRing.toCommSemiring (@NumberField.RingOfIntegers K inst)
                            (@NumberField.instCommRingRingOfIntegers K inst)))
                        (@AddCommGroup.toAddCommMonoid (Fin n → K)
                          (@Pi.addCommGroup (Fin n) (fun (a : Fin n) ↦ K) fun (i : Fin n) ↦
                            @Ring.toAddCommGroup K (@DivisionRing.toRing K (@Field.toDivisionRing K inst))))
                        (@Pi.Function.module (Fin n) (@NumberField.RingOfIntegers K inst) K
                          (@CommSemiring.toSemiring (@NumberField.RingOfIntegers K inst)
                            (@CommRing.toCommSemiring (@NumberField.RingOfIntegers K inst)
                              (@NumberField.instCommRingRingOfIntegers K inst)))
                          (@Semiring.toAddCommMonoid K
                            (@DivisionSemiring.toSemiring K (@Semifield.toDivisionSemiring K (@Field.toSemifield K inst))))
                          (@Algebra.toModule (@NumberField.RingOfIntegers K inst) K
                            (@CommRing.toCommSemiring (@NumberField.RingOfIntegers K inst)
                              (@NumberField.instCommRingRingOfIntegers K inst))
                            (@DivisionSemiring.toSemiring K (@Semifield.toDivisionSemiring K (@Field.toSemifield K inst)))
                            (@NumberField.RingOfIntegers.instAlgebra_1 K inst))))
                      (Fin n → K)
                      (@Submodule.setLike (@NumberField.RingOfIntegers K inst) (Fin n → K)
                        (@CommSemiring.toSemiring (@NumberField.RingOfIntegers K inst)
                          (@CommRing.toCommSemiring (@NumberField.RingOfIntegers K inst)
                            (@NumberField.instCommRingRingOfIntegers K inst)))
                        (@AddCommGroup.toAddCommMonoid (Fin n → K)
                          (@Pi.addCommGroup (Fin n) (fun (a : Fin n) ↦ K) fun (i : Fin n) ↦
                            @Ring.toAddCommGroup K (@DivisionRing.toRing K (@Field.toDivisionRing K inst))))
                        (@Pi.Function.module (Fin n) (@NumberField.RingOfIntegers K inst) K
                          (@CommSemiring.toSemiring (@NumberField.RingOfIntegers K inst)
                            (@CommRing.toCommSemiring (@NumberField.RingOfIntegers K inst)
                              (@NumberField.instCommRingRingOfIntegers K inst)))
                          (@Semiring.toAddCommMonoid K
                            (@DivisionSemiring.toSemiring K (@Semifield.toDivisionSemiring K (@Field.toSemifield K inst))))
                          (@Algebra.toModule (@NumberField.RingOfIntegers K inst) K
                            (@CommRing.toCommSemiring (@NumberField.RingOfIntegers K inst)
                              (@NumberField.instCommRingRingOfIntegers K inst))
                            (@DivisionSemiring.toSemiring K (@Semifield.toDivisionSemiring K (@Field.toSemifield K inst)))
                            (@NumberField.RingOfIntegers.instAlgebra_1 K inst)))))
                    (@UpperTheory.Reformulated.B.SelectionLemmas.dual (@NumberField.RingOfIntegers K inst) K (Fin n → K)
                      (@NumberField.instCommRingRingOfIntegers K inst) inst inst_2
                      (@NumberField.RingOfIntegers.instAlgebra_1 K inst)
                      (@Pi.addCommGroup (Fin n) (fun (a : Fin n) ↦ K) fun (i : Fin n) ↦
                        @Ring.toAddCommGroup K (@DivisionRing.toRing K (@Field.toDivisionRing K inst)))
                      (@Pi.Function.module (Fin n) K K
                        (@DivisionSemiring.toSemiring K (@Semifield.toDivisionSemiring K (@Field.toSemifield K inst)))
                        (@Semiring.toAddCommMonoid K
                          (@DivisionSemiring.toSemiring K (@Semifield.toDivisionSemiring K (@Field.toSemifield K inst))))
                        (@Semiring.toModule K
                          (@DivisionSemiring.toSemiring K (@Semifield.toDivisionSemiring K (@Field.toSemifield K inst)))))
                      (@Pi.Function.module (Fin n) (@NumberField.RingOfIntegers K inst) K
                        (@CommSemiring.toSemiring (@NumberField.RingOfIntegers K inst)
                          (@CommRing.toCommSemiring (@NumberField.RingOfIntegers K inst)
                            (@NumberField.instCommRingRingOfIntegers K inst)))
                        (@Semiring.toAddCommMonoid K
                          (@DivisionSemiring.toSemiring K (@Semifield.toDivisionSemiring K (@Field.toSemifield K inst))))
                        (@Algebra.toModule (@NumberField.RingOfIntegers K inst) K
                          (@CommRing.toCommSemiring (@NumberField.RingOfIntegers K inst)
                            (@NumberField.instCommRingRingOfIntegers K inst))
                          (@DivisionSemiring.toSemiring K (@Semifield.toDivisionSemiring K (@Field.toSemifield K inst)))
                          (@NumberField.RingOfIntegers.instAlgebra_1 K inst)))
                      (@Pi.isScalarTower (Fin n) (@NumberField.RingOfIntegers K inst) K (fun (a : Fin n) ↦ K)
                        (@Algebra.toSMul (@NumberField.RingOfIntegers K inst) K
                          (@CommRing.toCommSemiring (@NumberField.RingOfIntegers K inst)
                            (@NumberField.instCommRingRingOfIntegers K inst))
                          (@DivisionSemiring.toSemiring K (@Semifield.toDivisionSemiring K (@Field.toSemifield K inst)))
                          (@NumberField.RingOfIntegers.instAlgebra_1 K inst))
                        (fun (i : Fin n) ↦
                          @SemigroupAction.toSMul K ((fun (a : Fin n) ↦ K) i)
                            (@Monoid.toSemigroup K
                              (@Semiring.toMonoid K
                                (@DivisionSemiring.toSemiring K
                                  (@Semifield.toDivisionSemiring K (@Field.toSemifield K inst)))))
                            (@MulAction.toSemigroupAction K ((fun (a : Fin n) ↦ K) i)
                              (@Semiring.toMonoid K
                                (@DivisionSemiring.toSemiring K
                                  (@Semifield.toDivisionSemiring K (@Field.toSemifield K inst))))
                              ((fun (i : Fin n) ↦
                                  @DistribMulAction.toMulAction K ((fun (a : Fin n) ↦ K) i)
                                    (@Semiring.toMonoid K
                                      (@DivisionSemiring.toSemiring K
                                        (@Semifield.toDivisionSemiring K (@Field.toSemifield K inst))))
                                    ((fun (i : Fin n) ↦
                                        @AddCommMonoid.toAddMonoid ((fun (a : Fin n) ↦ K) i)
                                          ((fun (i : Fin n) ↦
                                              @Semiring.toAddCommMonoid K
                                                (@DivisionSemiring.toSemiring K
                                                  (@Semifield.toDivisionSemiring K (@Field.toSemifield K inst))))
                                            i))
                                      i)
                                    ((fun (i : Fin n) ↦
                                        @Module.toDistribMulAction K ((fun (a : Fin n) ↦ K) i)
                                          (@DivisionSemiring.toSemiring K
                                            (@Semifield.toDivisionSemiring K (@Field.toSemifield K inst)))
                                          ((fun (i : Fin n) ↦
                                              @Semiring.toAddCommMonoid K
                                                (@DivisionSemiring.toSemiring K
                                                  (@Semifield.toDivisionSemiring K (@Field.toSemifield K inst))))
                                            i)
                                          ((fun (i : Fin n) ↦
                                              @Semiring.toModule K
                                                (@DivisionSemiring.toSemiring K
                                                  (@Semifield.toDivisionSemiring K (@Field.toSemifield K inst))))
                                            i))
                                      i))
                                i)))
                        (fun (i : Fin n) ↦
                          @SemigroupAction.toSMul (@NumberField.RingOfIntegers K inst) ((fun (a : Fin n) ↦ K) i)
                            (@Monoid.toSemigroup (@NumberField.RingOfIntegers K inst)
                              (@Semiring.toMonoid (@NumberField.RingOfIntegers K inst)
                                (@CommSemiring.toSemiring (@NumberField.RingOfIntegers K inst)
                                  (@CommRing.toCommSemiring (@NumberField.RingOfIntegers K inst)
                                    (@NumberField.instCommRingRingOfIntegers K inst)))))
                            (@MulAction.toSemigroupAction (@NumberField.RingOfIntegers K inst) ((fun (a : Fin n) ↦ K) i)
                              (@Semiring.toMonoid (@NumberField.RingOfIntegers K inst)
                                (@CommSemiring.toSemiring (@NumberField.RingOfIntegers K inst)
                                  (@CommRing.toCommSemiring (@NumberField.RingOfIntegers K inst)
                                    (@NumberField.instCommRingRingOfIntegers K inst))))
                              ((fun (i : Fin n) ↦
                                  @DistribMulAction.toMulAction (@NumberField.RingOfIntegers K inst)
                                    ((fun (a : Fin n) ↦ K) i)
                                    (@Semiring.toMonoid (@NumberField.RingOfIntegers K inst)
                                      (@CommSemiring.toSemiring (@NumberField.RingOfIntegers K inst)
                                        (@CommRing.toCommSemiring (@NumberField.RingOfIntegers K inst)
                                          (@NumberField.instCommRingRingOfIntegers K inst))))
                                    ((fun (i : Fin n) ↦
                                        @AddCommMonoid.toAddMonoid ((fun (a : Fin n) ↦ K) i)
                                          ((fun (i : Fin n) ↦
                                              @Semiring.toAddCommMonoid K
                                                (@DivisionSemiring.toSemiring K
                                                  (@Semifield.toDivisionSemiring K (@Field.toSemifield K inst))))
                                            i))
                                      i)
                                    ((fun (i : Fin n) ↦
                                        @Module.toDistribMulAction (@NumberField.RingOfIntegers K inst)
                                          ((fun (a : Fin n) ↦ K) i)
                                          (@CommSemiring.toSemiring (@NumberField.RingOfIntegers K inst)
                                            (@CommRing.toCommSemiring (@NumberField.RingOfIntegers K inst)
                                              (@NumberField.instCommRingRingOfIntegers K inst)))
                                          ((fun (i : Fin n) ↦
                                              @Semiring.toAddCommMonoid K
                                                (@DivisionSemiring.toSemiring K
                                                  (@Semifield.toDivisionSemiring K (@Field.toSemifield K inst))))
                                            i)
                                          ((fun (i : Fin n) ↦
                                              @Algebra.toModule (@NumberField.RingOfIntegers K inst) K
                                                (@CommRing.toCommSemiring (@NumberField.RingOfIntegers K inst)
                                                  (@NumberField.instCommRingRingOfIntegers K inst))
                                                (@DivisionSemiring.toSemiring K
                                                  (@Semifield.toDivisionSemiring K (@Field.toSemifield K inst)))
                                                (@NumberField.RingOfIntegers.instAlgebra_1 K inst))
                                            i))
                                      i))
                                i)))
                        fun (i : Fin n) ↦
                        @IsScalarTower.right (@NumberField.RingOfIntegers K inst) K
                          (@CommRing.toCommSemiring (@NumberField.RingOfIntegers K inst)
                            (@NumberField.instCommRingRingOfIntegers K inst))
                          (@DivisionSemiring.toSemiring K (@Semifield.toDivisionSemiring K (@Field.toSemifield K inst)))
                          (@NumberField.RingOfIntegers.instAlgebra_1 K inst))
                      (@UpperTheory.Reformulated.B.SelectionLemmas.hform K inst inst_2 n H) M)
                    x →
                  @Membership.mem (Fin n → K)
                    (@Submodule (@NumberField.RingOfIntegers K inst) (Fin n → K)
                      (@CommSemiring.toSemiring (@NumberField.RingOfIntegers K inst)
                        (@CommRing.toCommSemiring (@NumberField.RingOfIntegers K inst)
                          (@NumberField.instCommRingRingOfIntegers K inst)))
                      (@Pi.addCommMonoid (Fin n) (fun (a : Fin n) ↦ K) fun (i : Fin n) ↦
                        @Semiring.toAddCommMonoid K
                          (@DivisionSemiring.toSemiring K (@Semifield.toDivisionSemiring K (@Field.toSemifield K inst))))
                      (@Pi.Function.module (Fin n) (@NumberField.RingOfIntegers K inst) K
                        (@CommSemiring.toSemiring (@NumberField.RingOfIntegers K inst)
                          (@CommRing.toCommSemiring (@NumberField.RingOfIntegers K inst)
                            (@NumberField.instCommRingRingOfIntegers K inst)))
                        (@Semiring.toAddCommMonoid K
                          (@DivisionSemiring.toSemiring K (@Semifield.toDivisionSemiring K (@Field.toSemifield K inst))))
                        (@Algebra.toModule (@NumberField.RingOfIntegers K inst) K
                          (@CommRing.toCommSemiring (@NumberField.RingOfIntegers K inst)
                            (@NumberField.instCommRingRingOfIntegers K inst))
                          (@DivisionSemiring.toSemiring K (@Semifield.toDivisionSemiring K (@Field.toSemifield K inst)))
                          (@NumberField.RingOfIntegers.instAlgebra_1 K inst))))
                    (@SetLike.instMembership
                      (@Submodule (@NumberField.RingOfIntegers K inst) (Fin n → K)
                        (@CommSemiring.toSemiring (@NumberField.RingOfIntegers K inst)
                          (@CommRing.toCommSemiring (@NumberField.RingOfIntegers K inst)
                            (@NumberField.instCommRingRingOfIntegers K inst)))
                        (@Pi.addCommMonoid (Fin n) (fun (a : Fin n) ↦ K) fun (i : Fin n) ↦
                          @Semiring.toAddCommMonoid K
                            (@DivisionSemiring.toSemiring K (@Semifield.toDivisionSemiring K (@Field.toSemifield K inst))))
                        (@Pi.Function.module (Fin n) (@NumberField.RingOfIntegers K inst) K
                          (@CommSemiring.toSemiring (@NumberField.RingOfIntegers K inst)
                            (@CommRing.toCommSemiring (@NumberField.RingOfIntegers K inst)
                              (@NumberField.instCommRingRingOfIntegers K inst)))
                          (@Semiring.toAddCommMonoid K
                            (@DivisionSemiring.toSemiring K (@Semifield.toDivisionSemiring K (@Field.toSemifield K inst))))
                          (@Algebra.toModule (@NumberField.RingOfIntegers K inst) K
                            (@CommRing.toCommSemiring (@NumberField.RingOfIntegers K inst)
                              (@NumberField.instCommRingRingOfIntegers K inst))
                            (@DivisionSemiring.toSemiring K (@Semifield.toDivisionSemiring K (@Field.toSemifield K inst)))
                            (@NumberField.RingOfIntegers.instAlgebra_1 K inst))))
                      (Fin n → K)
                      (@Submodule.setLike (@NumberField.RingOfIntegers K inst) (Fin n → K)
                        (@CommSemiring.toSemiring (@NumberField.RingOfIntegers K inst)
                          (@CommRing.toCommSemiring (@NumberField.RingOfIntegers K inst)
                            (@NumberField.instCommRingRingOfIntegers K inst)))
                        (@Pi.addCommMonoid (Fin n) (fun (a : Fin n) ↦ K) fun (i : Fin n) ↦
                          @Semiring.toAddCommMonoid K
                            (@DivisionSemiring.toSemiring K (@Semifield.toDivisionSemiring K (@Field.toSemifield K inst))))
                        (@Pi.Function.module (Fin n) (@NumberField.RingOfIntegers K inst) K
                          (@CommSemiring.toSemiring (@NumberField.RingOfIntegers K inst)
                            (@CommRing.toCommSemiring (@NumberField.RingOfIntegers K inst)
                              (@NumberField.instCommRingRingOfIntegers K inst)))
                          (@Semiring.toAddCommMonoid K
                            (@DivisionSemiring.toSemiring K (@Semifield.toDivisionSemiring K (@Field.toSemifield K inst))))
                          (@Algebra.toModule (@NumberField.RingOfIntegers K inst) K
                            (@CommRing.toCommSemiring (@NumberField.RingOfIntegers K inst)
                              (@NumberField.instCommRingRingOfIntegers K inst))
                            (@DivisionSemiring.toSemiring K (@Semifield.toDivisionSemiring K (@Field.toSemifield K inst)))
                            (@NumberField.RingOfIntegers.instAlgebra_1 K inst)))))
                    M
                    (@HSMul.hSMul (@NumberField.RingOfIntegers K inst) (Fin n → K) (Fin n → K)
                      (@instHSMul (@NumberField.RingOfIntegers K inst) (Fin n → K)
                        (@Function.hasSMul (Fin n) (@NumberField.RingOfIntegers K inst) K
                          (@Algebra.toSMul (@NumberField.RingOfIntegers K inst) K
                            (@CommRing.toCommSemiring (@NumberField.RingOfIntegers K inst)
                              (@NumberField.instCommRingRingOfIntegers K inst))
                            (@DivisionSemiring.toSemiring K (@Semifield.toDivisionSemiring K (@Field.toSemifield K inst)))
                            (@NumberField.RingOfIntegers.instAlgebra_1 K inst))))
                      (@HPow.hPow (@NumberField.RingOfIntegers K inst) Nat (@NumberField.RingOfIntegers K inst)
                        (@instHPow (@NumberField.RingOfIntegers K inst) Nat
                          (@NPow.toPow (@NumberField.RingOfIntegers K inst)
                            (@Monoid.toNPow (@NumberField.RingOfIntegers K inst)
                              (@Semiring.toMonoid (@NumberField.RingOfIntegers K inst)
                                (@CommSemiring.toSemiring (@NumberField.RingOfIntegers K inst)
                                  (@CommRing.toCommSemiring (@NumberField.RingOfIntegers K inst)
                                    (@NumberField.instCommRingRingOfIntegers K inst)))))))
                        (@Nat.cast (@NumberField.RingOfIntegers K inst)
                          (@AddMonoidWithOne.toNatCast (@NumberField.RingOfIntegers K inst)
                            (@AddGroupWithOne.toAddMonoidWithOne (@NumberField.RingOfIntegers K inst)
                              (@Ring.toAddGroupWithOne (@NumberField.RingOfIntegers K inst)
                                (@CommRing.toRing (@NumberField.RingOfIntegers K inst)
                                  (@NumberField.instCommRingRingOfIntegers K inst)))))
                          l)
                        g)
                      x)) →
              ∀
                (w :
                  @IsDedekindDomain.HeightOneSpectrum (@NumberField.RingOfIntegers K inst)
                    (@NumberField.instCommRingRingOfIntegers K inst))
                (e : Fin D → Fin D → K),
                @UpperTheory.Reformulated.B.SelectionLemmas.IsLocBasis K inst inst_2 D (@UpperTheory.Reformulated.B.SelectionLemmas.matLat K inst n D P M) w e →
                  @LE.le Int Int.instLEInt
                    (@UpperTheory.Reformulated.B.SelectionLemmas.vw K inst inst_1 w
                      (@UpperTheory.Reformulated.B.SelectionLemmas.gramR K inst inst_2 D D (@UpperTheory.Reformulated.B.SelectionLemmas.quotGram K inst inst_2 n D P H) e))
                    (@HMul.hMul Int Int Int (@instHMul Int Int.instMul)
                      (@HMul.hMul Int Int Int (@instHMul Int Int.instMul) (@Nat.cast Int instNatCastInt g)
                        (@Nat.cast Int instNatCastInt D))
                      (@UpperTheory.Reformulated.B.SelectionLemmas.vw K inst inst_1 w
                        (@Nat.cast K
                          (@AddMonoidWithOne.toNatCast K
                            (@AddGroupWithOne.toAddMonoidWithOne K
                              (@Ring.toAddGroupWithOne K (@DivisionRing.toRing K (@Field.toDivisionRing K inst)))))
                          l))) := by sorry
