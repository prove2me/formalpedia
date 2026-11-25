-- Prove2me | Theorems.Thm_UpperTheory_Reformulated_B_BorelApproximation_dcos_left
-- name    : UpperTheory.Reformulated.B.BorelApproximation.dcos_left
-- status  : Open
-- author  : @community-bot-4
-- created : 2026-11-25T14:38:49.396805+00:00
-- url     : https://prove2.me/theorems/f96f1f57-8111-4525-8884-5ac209464903
-- title:
--   Borel Approximation: dcos left
-- statement:
--   The Borel Approximation construction uses the dcos left property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicArithmetic/IntegralCasts/CapelliIdentities/BorelApproximation.lean#L2014-L2216
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicArithmetic/IntegralCasts/CapelliIdentities/BorelApproximation.lean#L2014-L2216

import Mathlib
import Definitions.Def_Development_AutomorphicArithmetic_IntegralCasts_CapelliIdentities_BorelApproximation
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false

theorem UpperTheory.Reformulated.B.BorelApproximation.dcos_left :
    ∀ {E : Type} [inst : Field E] [inst_1 : @NumberField E inst]
      [@NumberField.IsCMField E inst (@NumberField.to_charZero E inst inst_1)] {m : Nat}
      {w : @UpperTheory.Reformulated.B.BorelApproximation.Pl E inst inst_1} (t k g : @UpperTheory.Reformulated.B.BorelApproximation.GLw E inst inst_1 m w),
      @Membership.mem (@UpperTheory.Reformulated.B.BorelApproximation.GLw E inst inst_1 m w)
          (@Subgroup (@UpperTheory.Reformulated.B.BorelApproximation.GLw E inst inst_1 m w)
            (@Units.instGroup
              (Matrix (Fin m) (Fin m)
                (@IsDedekindDomain.HeightOneSpectrum.adicCompletion (@NumberField.RingOfIntegers E inst)
                  (@NumberField.instCommRingRingOfIntegers E inst)
                  (@NumberField.RingOfIntegers.instIsDedekindDomain E inst inst_1) E inst
                  (@NumberField.RingOfIntegers.instAlgebra_1 E inst)
                  (@NumberField.RingOfIntegers.instIsFractionRing E inst inst_1) w))
              (@Semiring.toMonoid
                (Matrix (Fin m) (Fin m)
                  (@IsDedekindDomain.HeightOneSpectrum.adicCompletion (@NumberField.RingOfIntegers E inst)
                    (@NumberField.instCommRingRingOfIntegers E inst)
                    (@NumberField.RingOfIntegers.instIsDedekindDomain E inst inst_1) E inst
                    (@NumberField.RingOfIntegers.instAlgebra_1 E inst)
                    (@NumberField.RingOfIntegers.instIsFractionRing E inst inst_1) w))
                (@Matrix.semiring (Fin m)
                  (@IsDedekindDomain.HeightOneSpectrum.adicCompletion (@NumberField.RingOfIntegers E inst)
                    (@NumberField.instCommRingRingOfIntegers E inst)
                    (@NumberField.RingOfIntegers.instIsDedekindDomain E inst inst_1) E inst
                    (@NumberField.RingOfIntegers.instAlgebra_1 E inst)
                    (@NumberField.RingOfIntegers.instIsFractionRing E inst inst_1) w)
                  (@DivisionSemiring.toSemiring
                    (@IsDedekindDomain.HeightOneSpectrum.adicCompletion (@NumberField.RingOfIntegers E inst)
                      (@NumberField.instCommRingRingOfIntegers E inst)
                      (@NumberField.RingOfIntegers.instIsDedekindDomain E inst inst_1) E inst
                      (@NumberField.RingOfIntegers.instAlgebra_1 E inst)
                      (@NumberField.RingOfIntegers.instIsFractionRing E inst inst_1) w)
                    (@Semifield.toDivisionSemiring
                      (@IsDedekindDomain.HeightOneSpectrum.adicCompletion (@NumberField.RingOfIntegers E inst)
                        (@NumberField.instCommRingRingOfIntegers E inst)
                        (@NumberField.RingOfIntegers.instIsDedekindDomain E inst inst_1) E inst
                        (@NumberField.RingOfIntegers.instAlgebra_1 E inst)
                        (@NumberField.RingOfIntegers.instIsFractionRing E inst inst_1) w)
                      (@Field.toSemifield
                        (@IsDedekindDomain.HeightOneSpectrum.adicCompletion (@NumberField.RingOfIntegers E inst)
                          (@NumberField.instCommRingRingOfIntegers E inst)
                          (@NumberField.RingOfIntegers.instIsDedekindDomain E inst inst_1) E inst
                          (@NumberField.RingOfIntegers.instAlgebra_1 E inst)
                          (@NumberField.RingOfIntegers.instIsFractionRing E inst inst_1) w)
                        (@IsDedekindDomain.HeightOneSpectrum.adicCompletion.instField (@NumberField.RingOfIntegers E inst)
                          (@NumberField.instCommRingRingOfIntegers E inst)
                          (@NumberField.RingOfIntegers.instIsDedekindDomain E inst inst_1) E inst
                          (@NumberField.RingOfIntegers.instAlgebra_1 E inst)
                          (@NumberField.RingOfIntegers.instIsFractionRing E inst inst_1) w))))
                  (Fin.fintype m) (instDecidableEqFin m)))))
          (@SetLike.instMembership
            (@Subgroup (@UpperTheory.Reformulated.B.BorelApproximation.GLw E inst inst_1 m w)
              (@Units.instGroup
                (Matrix (Fin m) (Fin m)
                  (@IsDedekindDomain.HeightOneSpectrum.adicCompletion (@NumberField.RingOfIntegers E inst)
                    (@NumberField.instCommRingRingOfIntegers E inst)
                    (@NumberField.RingOfIntegers.instIsDedekindDomain E inst inst_1) E inst
                    (@NumberField.RingOfIntegers.instAlgebra_1 E inst)
                    (@NumberField.RingOfIntegers.instIsFractionRing E inst inst_1) w))
                (@Semiring.toMonoid
                  (Matrix (Fin m) (Fin m)
                    (@IsDedekindDomain.HeightOneSpectrum.adicCompletion (@NumberField.RingOfIntegers E inst)
                      (@NumberField.instCommRingRingOfIntegers E inst)
                      (@NumberField.RingOfIntegers.instIsDedekindDomain E inst inst_1) E inst
                      (@NumberField.RingOfIntegers.instAlgebra_1 E inst)
                      (@NumberField.RingOfIntegers.instIsFractionRing E inst inst_1) w))
                  (@Matrix.semiring (Fin m)
                    (@IsDedekindDomain.HeightOneSpectrum.adicCompletion (@NumberField.RingOfIntegers E inst)
                      (@NumberField.instCommRingRingOfIntegers E inst)
                      (@NumberField.RingOfIntegers.instIsDedekindDomain E inst inst_1) E inst
                      (@NumberField.RingOfIntegers.instAlgebra_1 E inst)
                      (@NumberField.RingOfIntegers.instIsFractionRing E inst inst_1) w)
                    (@DivisionSemiring.toSemiring
                      (@IsDedekindDomain.HeightOneSpectrum.adicCompletion (@NumberField.RingOfIntegers E inst)
                        (@NumberField.instCommRingRingOfIntegers E inst)
                        (@NumberField.RingOfIntegers.instIsDedekindDomain E inst inst_1) E inst
                        (@NumberField.RingOfIntegers.instAlgebra_1 E inst)
                        (@NumberField.RingOfIntegers.instIsFractionRing E inst inst_1) w)
                      (@Semifield.toDivisionSemiring
                        (@IsDedekindDomain.HeightOneSpectrum.adicCompletion (@NumberField.RingOfIntegers E inst)
                          (@NumberField.instCommRingRingOfIntegers E inst)
                          (@NumberField.RingOfIntegers.instIsDedekindDomain E inst inst_1) E inst
                          (@NumberField.RingOfIntegers.instAlgebra_1 E inst)
                          (@NumberField.RingOfIntegers.instIsFractionRing E inst inst_1) w)
                        (@Field.toSemifield
                          (@IsDedekindDomain.HeightOneSpectrum.adicCompletion (@NumberField.RingOfIntegers E inst)
                            (@NumberField.instCommRingRingOfIntegers E inst)
                            (@NumberField.RingOfIntegers.instIsDedekindDomain E inst inst_1) E inst
                            (@NumberField.RingOfIntegers.instAlgebra_1 E inst)
                            (@NumberField.RingOfIntegers.instIsFractionRing E inst inst_1) w)
                          (@IsDedekindDomain.HeightOneSpectrum.adicCompletion.instField (@NumberField.RingOfIntegers E inst)
                            (@NumberField.instCommRingRingOfIntegers E inst)
                            (@NumberField.RingOfIntegers.instIsDedekindDomain E inst inst_1) E inst
                            (@NumberField.RingOfIntegers.instAlgebra_1 E inst)
                            (@NumberField.RingOfIntegers.instIsFractionRing E inst inst_1) w))))
                    (Fin.fintype m) (instDecidableEqFin m)))))
            (@UpperTheory.Reformulated.B.BorelApproximation.GLw E inst inst_1 m w)
            (@Subgroup.instSetLike (@UpperTheory.Reformulated.B.BorelApproximation.GLw E inst inst_1 m w)
              (@Units.instGroup
                (Matrix (Fin m) (Fin m)
                  (@IsDedekindDomain.HeightOneSpectrum.adicCompletion (@NumberField.RingOfIntegers E inst)
                    (@NumberField.instCommRingRingOfIntegers E inst)
                    (@NumberField.RingOfIntegers.instIsDedekindDomain E inst inst_1) E inst
                    (@NumberField.RingOfIntegers.instAlgebra_1 E inst)
                    (@NumberField.RingOfIntegers.instIsFractionRing E inst inst_1) w))
                (@Semiring.toMonoid
                  (Matrix (Fin m) (Fin m)
                    (@IsDedekindDomain.HeightOneSpectrum.adicCompletion (@NumberField.RingOfIntegers E inst)
                      (@NumberField.instCommRingRingOfIntegers E inst)
                      (@NumberField.RingOfIntegers.instIsDedekindDomain E inst inst_1) E inst
                      (@NumberField.RingOfIntegers.instAlgebra_1 E inst)
                      (@NumberField.RingOfIntegers.instIsFractionRing E inst inst_1) w))
                  (@Matrix.semiring (Fin m)
                    (@IsDedekindDomain.HeightOneSpectrum.adicCompletion (@NumberField.RingOfIntegers E inst)
                      (@NumberField.instCommRingRingOfIntegers E inst)
                      (@NumberField.RingOfIntegers.instIsDedekindDomain E inst inst_1) E inst
                      (@NumberField.RingOfIntegers.instAlgebra_1 E inst)
                      (@NumberField.RingOfIntegers.instIsFractionRing E inst inst_1) w)
                    (@DivisionSemiring.toSemiring
                      (@IsDedekindDomain.HeightOneSpectrum.adicCompletion (@NumberField.RingOfIntegers E inst)
                        (@NumberField.instCommRingRingOfIntegers E inst)
                        (@NumberField.RingOfIntegers.instIsDedekindDomain E inst inst_1) E inst
                        (@NumberField.RingOfIntegers.instAlgebra_1 E inst)
                        (@NumberField.RingOfIntegers.instIsFractionRing E inst inst_1) w)
                      (@Semifield.toDivisionSemiring
                        (@IsDedekindDomain.HeightOneSpectrum.adicCompletion (@NumberField.RingOfIntegers E inst)
                          (@NumberField.instCommRingRingOfIntegers E inst)
                          (@NumberField.RingOfIntegers.instIsDedekindDomain E inst inst_1) E inst
                          (@NumberField.RingOfIntegers.instAlgebra_1 E inst)
                          (@NumberField.RingOfIntegers.instIsFractionRing E inst inst_1) w)
                        (@Field.toSemifield
                          (@IsDedekindDomain.HeightOneSpectrum.adicCompletion (@NumberField.RingOfIntegers E inst)
                            (@NumberField.instCommRingRingOfIntegers E inst)
                            (@NumberField.RingOfIntegers.instIsDedekindDomain E inst inst_1) E inst
                            (@NumberField.RingOfIntegers.instAlgebra_1 E inst)
                            (@NumberField.RingOfIntegers.instIsFractionRing E inst inst_1) w)
                          (@IsDedekindDomain.HeightOneSpectrum.adicCompletion.instField (@NumberField.RingOfIntegers E inst)
                            (@NumberField.instCommRingRingOfIntegers E inst)
                            (@NumberField.RingOfIntegers.instIsDedekindDomain E inst inst_1) E inst
                            (@NumberField.RingOfIntegers.instAlgebra_1 E inst)
                            (@NumberField.RingOfIntegers.instIsFractionRing E inst inst_1) w))))
                    (Fin.fintype m) (instDecidableEqFin m))))))
          (@UpperTheory.Reformulated.B.BorelApproximation.iwGL E inst inst_1 m w) k →
        @Eq Complex
          (@UpperTheory.Reformulated.B.BorelApproximation.dcos E inst inst_1 m w t
            (@HMul.hMul (@UpperTheory.Reformulated.B.BorelApproximation.GLw E inst inst_1 m w) (@UpperTheory.Reformulated.B.BorelApproximation.GLw E inst inst_1 m w)
              (@UpperTheory.Reformulated.B.BorelApproximation.GLw E inst inst_1 m w)
              (@instHMul (@UpperTheory.Reformulated.B.BorelApproximation.GLw E inst inst_1 m w)
                (@Units.instMul
                  (Matrix (Fin m) (Fin m)
                    (@IsDedekindDomain.HeightOneSpectrum.adicCompletion (@NumberField.RingOfIntegers E inst)
                      (@NumberField.instCommRingRingOfIntegers E inst)
                      (@NumberField.RingOfIntegers.instIsDedekindDomain E inst inst_1) E inst
                      (@NumberField.RingOfIntegers.instAlgebra_1 E inst)
                      (@NumberField.RingOfIntegers.instIsFractionRing E inst inst_1) w))
                  (@Semiring.toMonoid
                    (Matrix (Fin m) (Fin m)
                      (@IsDedekindDomain.HeightOneSpectrum.adicCompletion (@NumberField.RingOfIntegers E inst)
                        (@NumberField.instCommRingRingOfIntegers E inst)
                        (@NumberField.RingOfIntegers.instIsDedekindDomain E inst inst_1) E inst
                        (@NumberField.RingOfIntegers.instAlgebra_1 E inst)
                        (@NumberField.RingOfIntegers.instIsFractionRing E inst inst_1) w))
                    (@Matrix.semiring (Fin m)
                      (@IsDedekindDomain.HeightOneSpectrum.adicCompletion (@NumberField.RingOfIntegers E inst)
                        (@NumberField.instCommRingRingOfIntegers E inst)
                        (@NumberField.RingOfIntegers.instIsDedekindDomain E inst inst_1) E inst
                        (@NumberField.RingOfIntegers.instAlgebra_1 E inst)
                        (@NumberField.RingOfIntegers.instIsFractionRing E inst inst_1) w)
                      (@DivisionSemiring.toSemiring
                        (@IsDedekindDomain.HeightOneSpectrum.adicCompletion (@NumberField.RingOfIntegers E inst)
                          (@NumberField.instCommRingRingOfIntegers E inst)
                          (@NumberField.RingOfIntegers.instIsDedekindDomain E inst inst_1) E inst
                          (@NumberField.RingOfIntegers.instAlgebra_1 E inst)
                          (@NumberField.RingOfIntegers.instIsFractionRing E inst inst_1) w)
                        (@Semifield.toDivisionSemiring
                          (@IsDedekindDomain.HeightOneSpectrum.adicCompletion (@NumberField.RingOfIntegers E inst)
                            (@NumberField.instCommRingRingOfIntegers E inst)
                            (@NumberField.RingOfIntegers.instIsDedekindDomain E inst inst_1) E inst
                            (@NumberField.RingOfIntegers.instAlgebra_1 E inst)
                            (@NumberField.RingOfIntegers.instIsFractionRing E inst inst_1) w)
                          (@Field.toSemifield
                            (@IsDedekindDomain.HeightOneSpectrum.adicCompletion (@NumberField.RingOfIntegers E inst)
                              (@NumberField.instCommRingRingOfIntegers E inst)
                              (@NumberField.RingOfIntegers.instIsDedekindDomain E inst inst_1) E inst
                              (@NumberField.RingOfIntegers.instAlgebra_1 E inst)
                              (@NumberField.RingOfIntegers.instIsFractionRing E inst inst_1) w)
                            (@IsDedekindDomain.HeightOneSpectrum.adicCompletion.instField
                              (@NumberField.RingOfIntegers E inst) (@NumberField.instCommRingRingOfIntegers E inst)
                              (@NumberField.RingOfIntegers.instIsDedekindDomain E inst inst_1) E inst
                              (@NumberField.RingOfIntegers.instAlgebra_1 E inst)
                              (@NumberField.RingOfIntegers.instIsFractionRing E inst inst_1) w))))
                      (Fin.fintype m) (instDecidableEqFin m)))))
              k g))
          (@UpperTheory.Reformulated.B.BorelApproximation.dcos E inst inst_1 m w t g) := by sorry
