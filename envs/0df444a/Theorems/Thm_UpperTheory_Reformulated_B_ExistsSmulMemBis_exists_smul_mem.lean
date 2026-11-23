-- Prove2me | Theorems.Thm_UpperTheory_Reformulated_B_ExistsSmulMemBis_exists_smul_mem
-- name    : UpperTheory.Reformulated.B.ExistsSmulMemBis.exists_smul_mem
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T18:06:05.729853+00:00
-- url     : https://prove2.me/theorems/43f855e3-27d8-423c-8308-07d77431da72
-- title:
--   Exists Smul Mem Bis: exists smul mem
-- statement:
--   The Exists Smul Mem Bis construction uses the exists smul mem property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicArithmetic/IntegralCasts/CapelliIdentities/ExistsSmulMemBis.lean#L36-L147
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicArithmetic/IntegralCasts/CapelliIdentities/ExistsSmulMemBis.lean#L36-L147

import Mathlib
import Definitions.Def_Formalism_WeaklyAdmissibleFiltrations_Statement
import Definitions.Def_Formalism_SharpRestriction_LevelLetterCocycles_LocCoh
import Definitions.Def_Development_AutomorphicArithmetic_IntegralCasts_CapelliIdentities_ExistsSmulMemBis
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false

theorem UpperTheory.Reformulated.B.ExistsSmulMemBis.exists_smul_mem :
    ∀ {G : Type} [inst : Group.{0} G] [inst_1 : TopologicalSpace.{0} G] {Qp LL O : Type} [inst_2 : Field.{0} Qp]
      [inst_3 : Field.{0} LL]
      [inst_4 :
        @Algebra.{0, 0} Qp LL (@Semifield.toCommSemiring.{0} Qp (@Field.toSemifield.{0} Qp inst_2))
          (@DivisionSemiring.toSemiring.{0} LL (@Semifield.toDivisionSemiring.{0} LL (@Field.toSemifield.{0} LL inst_3)))]
      [inst_5 : CommRing.{0} O]
      [inst_6 :
        @Algebra.{0, 0} O LL (@CommRing.toCommSemiring.{0} O inst_5)
          (@DivisionSemiring.toSemiring.{0} LL (@Semifield.toDivisionSemiring.{0} LL (@Field.toSemifield.{0} LL inst_3)))]
      [inst_7 : TopologicalSpace.{0} LL]
      (A : @Formalism.MainNotions.N.GRep G inst inst_1 Qp LL O inst_2 inst_3 inst_4 inst_5 inst_6 inst_7)
      (LA :
        @Formalism.WeaklyAdmissibleFiltrations.Lattice G inst LL inst_3 O inst_5
          (@Formalism.MainNotions.N.GRep.V G inst inst_1 Qp LL O inst_2 inst_3 inst_4 inst_5 inst_6 inst_7 A)
          (@Formalism.MainNotions.N.GRep.acg G inst inst_1 Qp LL O inst_2 inst_3 inst_4 inst_5 inst_6 inst_7 A)
          (@Formalism.MainNotions.N.GRep.modLL G inst inst_1 Qp LL O inst_2 inst_3 inst_4 inst_5 inst_6 inst_7 A)
          (@Formalism.MainNotions.N.GRep.modO G inst inst_1 Qp LL O inst_2 inst_3 inst_4 inst_5 inst_6 inst_7 A)
          (@Formalism.MainNotions.N.GRep.ρ G inst inst_1 Qp LL O inst_2 inst_3 inst_4 inst_5 inst_6 inst_7 A))
      [@IsDomain.{0} O (@CommSemiring.toSemiring.{0} O (@CommRing.toCommSemiring.{0} O inst_5))]
      [@IsFractionRing.{0, 0} O (@CommRing.toCommSemiring.{0} O inst_5) LL
          (@Semifield.toCommSemiring.{0} LL (@Field.toSemifield.{0} LL inst_3)) inst_6]
      (v : @Formalism.MainNotions.N.GRep.V G inst inst_1 Qp LL O inst_2 inst_3 inst_4 inst_5 inst_6 inst_7 A),
      ∃ (a : O),
        And
          (@Ne.{1} O a
            (@OfNat.ofNat.{0} O (nat_lit 0)
              (@Zero.toOfNat0.{0} O
                (@MulZeroClass.toZero.{0} O
                  (@instMulZeroClassOfSemiring.{0} O
                    (@CommSemiring.toSemiring.{0} O (@CommRing.toCommSemiring.{0} O inst_5)))))))
          (@Membership.mem.{0, 0} (@Formalism.MainNotions.N.GRep.V G inst inst_1 Qp LL O inst_2 inst_3 inst_4 inst_5 inst_6 inst_7 A)
            (@Submodule.{0, 0} O (@Formalism.MainNotions.N.GRep.V G inst inst_1 Qp LL O inst_2 inst_3 inst_4 inst_5 inst_6 inst_7 A)
              (@CommSemiring.toSemiring.{0} O (@CommRing.toCommSemiring.{0} O inst_5))
              (@AddCommGroup.toAddCommMonoid.{0}
                (@Formalism.MainNotions.N.GRep.V G inst inst_1 Qp LL O inst_2 inst_3 inst_4 inst_5 inst_6 inst_7 A)
                (@Formalism.MainNotions.N.GRep.acg G inst inst_1 Qp LL O inst_2 inst_3 inst_4 inst_5 inst_6 inst_7 A))
              (@Formalism.MainNotions.N.GRep.modO G inst inst_1 Qp LL O inst_2 inst_3 inst_4 inst_5 inst_6 inst_7 A))
            (@SetLike.instMembership.{0, 0}
              (@Submodule.{0, 0} O (@Formalism.MainNotions.N.GRep.V G inst inst_1 Qp LL O inst_2 inst_3 inst_4 inst_5 inst_6 inst_7 A)
                (@CommSemiring.toSemiring.{0} O (@CommRing.toCommSemiring.{0} O inst_5))
                (@AddCommGroup.toAddCommMonoid.{0}
                  (@Formalism.MainNotions.N.GRep.V G inst inst_1 Qp LL O inst_2 inst_3 inst_4 inst_5 inst_6 inst_7 A)
                  (@Formalism.MainNotions.N.GRep.acg G inst inst_1 Qp LL O inst_2 inst_3 inst_4 inst_5 inst_6 inst_7 A))
                (@Formalism.MainNotions.N.GRep.modO G inst inst_1 Qp LL O inst_2 inst_3 inst_4 inst_5 inst_6 inst_7 A))
              (@Formalism.MainNotions.N.GRep.V G inst inst_1 Qp LL O inst_2 inst_3 inst_4 inst_5 inst_6 inst_7 A)
              (@Submodule.setLike.{0, 0} O
                (@Formalism.MainNotions.N.GRep.V G inst inst_1 Qp LL O inst_2 inst_3 inst_4 inst_5 inst_6 inst_7 A)
                (@CommSemiring.toSemiring.{0} O (@CommRing.toCommSemiring.{0} O inst_5))
                (@AddCommGroup.toAddCommMonoid.{0}
                  (@Formalism.MainNotions.N.GRep.V G inst inst_1 Qp LL O inst_2 inst_3 inst_4 inst_5 inst_6 inst_7 A)
                  (@Formalism.MainNotions.N.GRep.acg G inst inst_1 Qp LL O inst_2 inst_3 inst_4 inst_5 inst_6 inst_7 A))
                (@Formalism.MainNotions.N.GRep.modO G inst inst_1 Qp LL O inst_2 inst_3 inst_4 inst_5 inst_6 inst_7 A)))
            (@Formalism.WeaklyAdmissibleFiltrations.Lattice.T G inst LL inst_3 O inst_5
              (@Formalism.MainNotions.N.GRep.V G inst inst_1 Qp LL O inst_2 inst_3 inst_4 inst_5 inst_6 inst_7 A)
              (@Formalism.MainNotions.N.GRep.acg G inst inst_1 Qp LL O inst_2 inst_3 inst_4 inst_5 inst_6 inst_7 A)
              (@Formalism.MainNotions.N.GRep.modLL G inst inst_1 Qp LL O inst_2 inst_3 inst_4 inst_5 inst_6 inst_7 A)
              (@Formalism.MainNotions.N.GRep.modO G inst inst_1 Qp LL O inst_2 inst_3 inst_4 inst_5 inst_6 inst_7 A)
              (@Formalism.MainNotions.N.GRep.ρ G inst inst_1 Qp LL O inst_2 inst_3 inst_4 inst_5 inst_6 inst_7 A) LA)
            (@HSMul.hSMul.{0, 0, 0} O (@Formalism.MainNotions.N.GRep.V G inst inst_1 Qp LL O inst_2 inst_3 inst_4 inst_5 inst_6 inst_7 A)
              (@Formalism.MainNotions.N.GRep.V G inst inst_1 Qp LL O inst_2 inst_3 inst_4 inst_5 inst_6 inst_7 A)
              (@instHSMul.{0, 0} O (@Formalism.MainNotions.N.GRep.V G inst inst_1 Qp LL O inst_2 inst_3 inst_4 inst_5 inst_6 inst_7 A)
                (@SMulZeroClass.toSMul.{0, 0} O
                  (@Formalism.MainNotions.N.GRep.V G inst inst_1 Qp LL O inst_2 inst_3 inst_4 inst_5 inst_6 inst_7 A)
                  (@AddZero.toZero.{0} (@Formalism.MainNotions.N.GRep.V G inst inst_1 Qp LL O inst_2 inst_3 inst_4 inst_5 inst_6 inst_7 A)
                    (@AddZeroClass.toAddZero.{0}
                      (@Formalism.MainNotions.N.GRep.V G inst inst_1 Qp LL O inst_2 inst_3 inst_4 inst_5 inst_6 inst_7 A)
                      (@AddMonoid.toAddZeroClass.{0}
                        (@Formalism.MainNotions.N.GRep.V G inst inst_1 Qp LL O inst_2 inst_3 inst_4 inst_5 inst_6 inst_7 A)
                        (@SubNegMonoid.toAddMonoid.{0}
                          (@Formalism.MainNotions.N.GRep.V G inst inst_1 Qp LL O inst_2 inst_3 inst_4 inst_5 inst_6 inst_7 A)
                          (@AddGroup.toSubNegMonoid.{0}
                            (@Formalism.MainNotions.N.GRep.V G inst inst_1 Qp LL O inst_2 inst_3 inst_4 inst_5 inst_6 inst_7 A)
                            (@AddCommGroup.toAddGroup.{0}
                              (@Formalism.MainNotions.N.GRep.V G inst inst_1 Qp LL O inst_2 inst_3 inst_4 inst_5 inst_6 inst_7 A)
                              (@Formalism.MainNotions.N.GRep.acg G inst inst_1 Qp LL O inst_2 inst_3 inst_4 inst_5 inst_6 inst_7 A)))))))
                  (@DistribSMul.toSMulZeroClass.{0, 0} O
                    (@Formalism.MainNotions.N.GRep.V G inst inst_1 Qp LL O inst_2 inst_3 inst_4 inst_5 inst_6 inst_7 A)
                    (@AddMonoid.toAddZeroClass.{0}
                      (@Formalism.MainNotions.N.GRep.V G inst inst_1 Qp LL O inst_2 inst_3 inst_4 inst_5 inst_6 inst_7 A)
                      (@SubNegMonoid.toAddMonoid.{0}
                        (@Formalism.MainNotions.N.GRep.V G inst inst_1 Qp LL O inst_2 inst_3 inst_4 inst_5 inst_6 inst_7 A)
                        (@AddGroup.toSubNegMonoid.{0}
                          (@Formalism.MainNotions.N.GRep.V G inst inst_1 Qp LL O inst_2 inst_3 inst_4 inst_5 inst_6 inst_7 A)
                          (@AddCommGroup.toAddGroup.{0}
                            (@Formalism.MainNotions.N.GRep.V G inst inst_1 Qp LL O inst_2 inst_3 inst_4 inst_5 inst_6 inst_7 A)
                            (@Formalism.MainNotions.N.GRep.acg G inst inst_1 Qp LL O inst_2 inst_3 inst_4 inst_5 inst_6 inst_7 A)))))
                    (@DistribMulAction.toDistribSMul.{0, 0} O
                      (@Formalism.MainNotions.N.GRep.V G inst inst_1 Qp LL O inst_2 inst_3 inst_4 inst_5 inst_6 inst_7 A)
                      (@Semiring.toMonoid.{0} O (@CommSemiring.toSemiring.{0} O (@CommRing.toCommSemiring.{0} O inst_5)))
                      (@SubNegMonoid.toAddMonoid.{0}
                        (@Formalism.MainNotions.N.GRep.V G inst inst_1 Qp LL O inst_2 inst_3 inst_4 inst_5 inst_6 inst_7 A)
                        (@AddGroup.toSubNegMonoid.{0}
                          (@Formalism.MainNotions.N.GRep.V G inst inst_1 Qp LL O inst_2 inst_3 inst_4 inst_5 inst_6 inst_7 A)
                          (@AddCommGroup.toAddGroup.{0}
                            (@Formalism.MainNotions.N.GRep.V G inst inst_1 Qp LL O inst_2 inst_3 inst_4 inst_5 inst_6 inst_7 A)
                            (@Formalism.MainNotions.N.GRep.acg G inst inst_1 Qp LL O inst_2 inst_3 inst_4 inst_5 inst_6 inst_7 A))))
                      (@Module.toDistribMulAction.{0, 0} O
                        (@Formalism.MainNotions.N.GRep.V G inst inst_1 Qp LL O inst_2 inst_3 inst_4 inst_5 inst_6 inst_7 A)
                        (@CommSemiring.toSemiring.{0} O (@CommRing.toCommSemiring.{0} O inst_5))
                        (@AddCommGroup.toAddCommMonoid.{0}
                          (@Formalism.MainNotions.N.GRep.V G inst inst_1 Qp LL O inst_2 inst_3 inst_4 inst_5 inst_6 inst_7 A)
                          (@Formalism.MainNotions.N.GRep.acg G inst inst_1 Qp LL O inst_2 inst_3 inst_4 inst_5 inst_6 inst_7 A))
                        (@Formalism.MainNotions.N.GRep.modO G inst inst_1 Qp LL O inst_2 inst_3 inst_4 inst_5 inst_6 inst_7 A))))))
              a v)) := by sorry
