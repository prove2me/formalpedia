-- Prove2me | Theorems.Thm_UpperTheory_Reformulated_B_BlockHomomorphism_exists_fixK
-- name    : UpperTheory.Reformulated.B.BlockHomomorphism.exists_fixK
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T20:49:07.767323+00:00
-- url     : https://prove2.me/theorems/c30d0e69-b7f2-41df-87ea-0ad7e4c9f2da
-- title:
--   Block Homomorphism: exists fix K
-- statement:
--   The Block Homomorphism construction uses the exists fix K property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicArithmetic/IntegralCasts/CapelliIdentities/BlockHomomorphism.lean#L1212-L1484
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicArithmetic/IntegralCasts/CapelliIdentities/BlockHomomorphism.lean#L1212-L1484

import Mathlib
import Definitions.Def_Development_AutomorphicArithmetic_IntegralCasts_CapelliIdentities_BlockHomomorphism
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false

theorem UpperTheory.Reformulated.B.BlockHomomorphism.exists_fixK :
    ∀ {k : Type} [inst : Field k]
      [inst_1 :
        @ValuativeRel k (@DivisionSemiring.toSemiring k (@Semifield.toDivisionSemiring k (@Field.toSemifield k inst)))]
      [inst_2 : TopologicalSpace k] [@IsNonarchimedeanLocalField k inst inst_1 inst_2] {m N : Nat}
      {h :
        @LE.le Nat instLENat
          (@HAdd.hAdd Nat Nat Nat (@instHAdd Nat instAddNat) m (@OfNat.ofNat Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))) N}
      {V : Type} [inst_4 : AddCommGroup V]
      [inst_5 : @_root_.Module Complex V Complex.instSemiring (@AddCommGroup.toAddCommMonoid V inst_4)]
      {π :
        @Representation Complex
          (@Matrix.GeneralLinearGroup (Fin N) k (instDecidableEqFin N) (Fin.fintype N)
            (@DivisionSemiring.toSemiring k (@Semifield.toDivisionSemiring k (@Field.toSemifield k inst))))
          V Complex.instSemiring
          (@Units.instMonoid (Matrix (Fin N) (Fin N) k)
            (@Semiring.toMonoid (Matrix (Fin N) (Fin N) k)
              (@Matrix.semiring (Fin N) k
                (@DivisionSemiring.toSemiring k (@Semifield.toDivisionSemiring k (@Field.toSemifield k inst)))
                (Fin.fintype N) (instDecidableEqFin N))))
          (@AddCommGroup.toAddCommMonoid V inst_4) inst_5},
      @UpperTheory.Reformulated.B.BlockHomomorphism.IsSmooth Complex
          (@Matrix.GeneralLinearGroup (Fin N) k (instDecidableEqFin N) (Fin.fintype N)
            (@DivisionSemiring.toSemiring k (@Semifield.toDivisionSemiring k (@Field.toSemifield k inst))))
          V Complex.instField
          (@Units.instGroup (Matrix (Fin N) (Fin N) k)
            (@Semiring.toMonoid (Matrix (Fin N) (Fin N) k)
              (@Matrix.semiring (Fin N) k
                (@DivisionSemiring.toSemiring k (@Semifield.toDivisionSemiring k (@Field.toSemifield k inst)))
                (Fin.fintype N) (instDecidableEqFin N))))
          inst_4 inst_5
          (@Units.instTopologicalSpaceUnits (Matrix (Fin N) (Fin N) k)
            (@instTopologicalSpaceMatrix (Fin N) (Fin N) k inst_2)
            (@Semiring.toMonoid (Matrix (Fin N) (Fin N) k)
              (@Matrix.semiring (Fin N) k
                (@DivisionSemiring.toSemiring k (@Semifield.toDivisionSemiring k (@Field.toSemifield k inst)))
                (Fin.fintype N) (instDecidableEqFin N))))
          π →
        ∀ (v w : V),
          ∃ (K :
            @Subgroup
              (@Matrix.GeneralLinearGroup
                (Fin
                  (@HAdd.hAdd Nat Nat Nat (@instHAdd Nat instAddNat) m
                    (@OfNat.ofNat Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
                k
                (instDecidableEqFin
                  (@HAdd.hAdd Nat Nat Nat (@instHAdd Nat instAddNat) m
                    (@OfNat.ofNat Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
                (Fin.fintype
                  (@HAdd.hAdd Nat Nat Nat (@instHAdd Nat instAddNat) m
                    (@OfNat.ofNat Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
                (@DivisionSemiring.toSemiring k (@Semifield.toDivisionSemiring k (@Field.toSemifield k inst))))
              (@Units.instGroup
                (Matrix
                  (Fin
                    (@HAdd.hAdd Nat Nat Nat (@instHAdd Nat instAddNat) m
                      (@OfNat.ofNat Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
                  (Fin
                    (@HAdd.hAdd Nat Nat Nat (@instHAdd Nat instAddNat) m
                      (@OfNat.ofNat Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
                  k)
                (@Semiring.toMonoid
                  (Matrix
                    (Fin
                      (@HAdd.hAdd Nat Nat Nat (@instHAdd Nat instAddNat) m
                        (@OfNat.ofNat Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
                    (Fin
                      (@HAdd.hAdd Nat Nat Nat (@instHAdd Nat instAddNat) m
                        (@OfNat.ofNat Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
                    k)
                  (@Matrix.semiring
                    (Fin
                      (@HAdd.hAdd Nat Nat Nat (@instHAdd Nat instAddNat) m
                        (@OfNat.ofNat Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
                    k (@DivisionSemiring.toSemiring k (@Semifield.toDivisionSemiring k (@Field.toSemifield k inst)))
                    (Fin.fintype
                      (@HAdd.hAdd Nat Nat Nat (@instHAdd Nat instAddNat) m
                        (@OfNat.ofNat Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
                    (instDecidableEqFin
                      (@HAdd.hAdd Nat Nat Nat (@instHAdd Nat instAddNat) m
                        (@OfNat.ofNat Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))))))),
            And
              (@IsOpen
                (@Matrix.GeneralLinearGroup
                  (Fin
                    (@HAdd.hAdd Nat Nat Nat (@instHAdd Nat instAddNat) m
                      (@OfNat.ofNat Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
                  k
                  (instDecidableEqFin
                    (@HAdd.hAdd Nat Nat Nat (@instHAdd Nat instAddNat) m
                      (@OfNat.ofNat Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
                  (Fin.fintype
                    (@HAdd.hAdd Nat Nat Nat (@instHAdd Nat instAddNat) m
                      (@OfNat.ofNat Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
                  (@DivisionSemiring.toSemiring k (@Semifield.toDivisionSemiring k (@Field.toSemifield k inst))))
                (@Units.instTopologicalSpaceUnits
                  (Matrix
                    (Fin
                      (@HAdd.hAdd Nat Nat Nat (@instHAdd Nat instAddNat) m
                        (@OfNat.ofNat Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
                    (Fin
                      (@HAdd.hAdd Nat Nat Nat (@instHAdd Nat instAddNat) m
                        (@OfNat.ofNat Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
                    k)
                  (@instTopologicalSpaceMatrix
                    (Fin
                      (@HAdd.hAdd Nat Nat Nat (@instHAdd Nat instAddNat) m
                        (@OfNat.ofNat Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
                    (Fin
                      (@HAdd.hAdd Nat Nat Nat (@instHAdd Nat instAddNat) m
                        (@OfNat.ofNat Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
                    k inst_2)
                  (@Semiring.toMonoid
                    (Matrix
                      (Fin
                        (@HAdd.hAdd Nat Nat Nat (@instHAdd Nat instAddNat) m
                          (@OfNat.ofNat Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
                      (Fin
                        (@HAdd.hAdd Nat Nat Nat (@instHAdd Nat instAddNat) m
                          (@OfNat.ofNat Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
                      k)
                    (@Matrix.semiring
                      (Fin
                        (@HAdd.hAdd Nat Nat Nat (@instHAdd Nat instAddNat) m
                          (@OfNat.ofNat Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
                      k (@DivisionSemiring.toSemiring k (@Semifield.toDivisionSemiring k (@Field.toSemifield k inst)))
                      (Fin.fintype
                        (@HAdd.hAdd Nat Nat Nat (@instHAdd Nat instAddNat) m
                          (@OfNat.ofNat Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
                      (instDecidableEqFin
                        (@HAdd.hAdd Nat Nat Nat (@instHAdd Nat instAddNat) m
                          (@OfNat.ofNat Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))))))
                (@SetLike.coe
                  (@Subgroup
                    (@Matrix.GeneralLinearGroup
                      (Fin
                        (@HAdd.hAdd Nat Nat Nat (@instHAdd Nat instAddNat) m
                          (@OfNat.ofNat Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
                      k
                      (instDecidableEqFin
                        (@HAdd.hAdd Nat Nat Nat (@instHAdd Nat instAddNat) m
                          (@OfNat.ofNat Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
                      (Fin.fintype
                        (@HAdd.hAdd Nat Nat Nat (@instHAdd Nat instAddNat) m
                          (@OfNat.ofNat Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
                      (@DivisionSemiring.toSemiring k (@Semifield.toDivisionSemiring k (@Field.toSemifield k inst))))
                    (@Units.instGroup
                      (Matrix
                        (Fin
                          (@HAdd.hAdd Nat Nat Nat (@instHAdd Nat instAddNat) m
                            (@OfNat.ofNat Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
                        (Fin
                          (@HAdd.hAdd Nat Nat Nat (@instHAdd Nat instAddNat) m
                            (@OfNat.ofNat Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
                        k)
                      (@Semiring.toMonoid
                        (Matrix
                          (Fin
                            (@HAdd.hAdd Nat Nat Nat (@instHAdd Nat instAddNat) m
                              (@OfNat.ofNat Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
                          (Fin
                            (@HAdd.hAdd Nat Nat Nat (@instHAdd Nat instAddNat) m
                              (@OfNat.ofNat Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
                          k)
                        (@Matrix.semiring
                          (Fin
                            (@HAdd.hAdd Nat Nat Nat (@instHAdd Nat instAddNat) m
                              (@OfNat.ofNat Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
                          k (@DivisionSemiring.toSemiring k (@Semifield.toDivisionSemiring k (@Field.toSemifield k inst)))
                          (Fin.fintype
                            (@HAdd.hAdd Nat Nat Nat (@instHAdd Nat instAddNat) m
                              (@OfNat.ofNat Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
                          (instDecidableEqFin
                            (@HAdd.hAdd Nat Nat Nat (@instHAdd Nat instAddNat) m
                              (@OfNat.ofNat Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))))))
                  (@Matrix.GeneralLinearGroup
                    (Fin
                      (@HAdd.hAdd Nat Nat Nat (@instHAdd Nat instAddNat) m
                        (@OfNat.ofNat Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
                    k
                    (instDecidableEqFin
                      (@HAdd.hAdd Nat Nat Nat (@instHAdd Nat instAddNat) m
                        (@OfNat.ofNat Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
                    (Fin.fintype
                      (@HAdd.hAdd Nat Nat Nat (@instHAdd Nat instAddNat) m
                        (@OfNat.ofNat Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
                    (@DivisionSemiring.toSemiring k (@Semifield.toDivisionSemiring k (@Field.toSemifield k inst))))
                  (@Subgroup.instSetLike
                    (@Matrix.GeneralLinearGroup
                      (Fin
                        (@HAdd.hAdd Nat Nat Nat (@instHAdd Nat instAddNat) m
                          (@OfNat.ofNat Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
                      k
                      (instDecidableEqFin
                        (@HAdd.hAdd Nat Nat Nat (@instHAdd Nat instAddNat) m
                          (@OfNat.ofNat Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
                      (Fin.fintype
                        (@HAdd.hAdd Nat Nat Nat (@instHAdd Nat instAddNat) m
                          (@OfNat.ofNat Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
                      (@DivisionSemiring.toSemiring k (@Semifield.toDivisionSemiring k (@Field.toSemifield k inst))))
                    (@Units.instGroup
                      (Matrix
                        (Fin
                          (@HAdd.hAdd Nat Nat Nat (@instHAdd Nat instAddNat) m
                            (@OfNat.ofNat Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
                        (Fin
                          (@HAdd.hAdd Nat Nat Nat (@instHAdd Nat instAddNat) m
                            (@OfNat.ofNat Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
                        k)
                      (@Semiring.toMonoid
                        (Matrix
                          (Fin
                            (@HAdd.hAdd Nat Nat Nat (@instHAdd Nat instAddNat) m
                              (@OfNat.ofNat Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
                          (Fin
                            (@HAdd.hAdd Nat Nat Nat (@instHAdd Nat instAddNat) m
                              (@OfNat.ofNat Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
                          k)
                        (@Matrix.semiring
                          (Fin
                            (@HAdd.hAdd Nat Nat Nat (@instHAdd Nat instAddNat) m
                              (@OfNat.ofNat Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
                          k (@DivisionSemiring.toSemiring k (@Semifield.toDivisionSemiring k (@Field.toSemifield k inst)))
                          (Fin.fintype
                            (@HAdd.hAdd Nat Nat Nat (@instHAdd Nat instAddNat) m
                              (@OfNat.ofNat Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
                          (instDecidableEqFin
                            (@HAdd.hAdd Nat Nat Nat (@instHAdd Nat instAddNat) m
                              (@OfNat.ofNat Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))))))
                  K))
              (And
                (@UpperTheory.Reformulated.B.BlockHomomorphism.FixK k inst m N
                  (@Decidable.byContradiction
                    (@LE.le Nat instLENat
                      (@HAdd.hAdd Nat Nat Nat (@instHAdd Nat instAddNat) m
                        (@OfNat.ofNat Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
                      N)
                    ((@HAdd.hAdd Nat Nat Nat (@instHAdd Nat instAddNat) m
                          (@OfNat.ofNat Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))).decLe
                      N)
                    fun
                      (a :
                        Not
                          (@LE.le Nat instLENat
                            (@HAdd.hAdd Nat Nat Nat (@instHAdd Nat instAddNat) m
                              (@OfNat.ofNat Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
                            N)) ↦
                    @UpperTheory.Reformulated.B.BlockHomomorphism.aux9 m N h a)
                  V inst_4 inst_5 π K v)
                (@UpperTheory.Reformulated.B.BlockHomomorphism.FixK k inst m N
                  (@Decidable.byContradiction
                    (@LE.le Nat instLENat
                      (@HAdd.hAdd Nat Nat Nat (@instHAdd Nat instAddNat) m
                        (@OfNat.ofNat Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
                      N)
                    ((@HAdd.hAdd Nat Nat Nat (@instHAdd Nat instAddNat) m
                          (@OfNat.ofNat Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))).decLe
                      N)
                    fun
                      (a :
                        Not
                          (@LE.le Nat instLENat
                            (@HAdd.hAdd Nat Nat Nat (@instHAdd Nat instAddNat) m
                              (@OfNat.ofNat Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
                            N)) ↦
                    @UpperTheory.Reformulated.B.BlockHomomorphism.aux9 m N h a)
                  V inst_4 inst_5 π K w)) := by sorry
