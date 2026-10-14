-- Prove2me | Theorems.Thm_ThreeSum_HashFamily_linear_fiber_card
-- name    : ThreeSum.HashFamily.linear_fiber_card
-- status  : Open
-- author  : @wurtle
-- created : 2026-10-14T06:41:33.999475+00:00
-- url     : https://prove2.me/theorems/d725b305-a7ea-4b41-8d8b-bf0916303a33
-- title:
--   Exact fiber cardinalities of a finite surjective linear map
-- statement:
--   Let $K$ be a field and let $V,W$ be $K$-vector spaces with finite underlying sets. If $f:V\to W$ is a surjective linear map, then for every target $y\in W$,
--
--   $$
--   |W|\,\bigl|f^{-1}(\{y\})\bigr|=|V|.
--   $$
--
--   The statement counts the full domain and every target fiber as natural numbers. It does not require a separate assumption that the field is finite.
--
--   This is the exact counting form of uniformity for a surjective linear map: uniform enumeration of domain elements gives equal multiplicity to every target. It is used to establish finite hash-output probabilities without approximate counting.
-- source:
--   https://github.com/c0ldzy17/three-sum-lean/blob/2b639655e07421b9ac743de9090459bab473a7c0/Submission/ThreeSum/HashFamily.lean#L174-L194

import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Data.Fin.VecNotation
import Mathlib.Data.Real.Basic
import Mathlib.GroupTheory.Index
import Mathlib.LinearAlgebra.Dual.Lemmas
import Mathlib.LinearAlgebra.Matrix.Dual
import Mathlib.LinearAlgebra.Matrix.ToLin
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Push
import Mathlib.Tactic.Ring


set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option Elab.async false

universe u_2 u_5 u_6

theorem ThreeSum.HashFamily.linear_fiber_card : ∀ {K : Type u_2} [inst : Field.{u_2} K] {V : Type u_5} {W : Type u_6} [inst_1 : AddCommGroup.{u_5} V]
  [inst_2 :
    @_root_.Module.{u_2, u_5} K V
      (@DivisionSemiring.toSemiring.{u_2} K (@Semifield.toDivisionSemiring.{u_2} K (@Field.toSemifield.{u_2} K inst)))
      (@AddCommGroup.toAddCommMonoid.{u_5} V inst_1)]
  [inst_3 : AddCommGroup.{u_6} W]
  [inst_4 :
    @_root_.Module.{u_2, u_6} K W
      (@DivisionSemiring.toSemiring.{u_2} K (@Semifield.toDivisionSemiring.{u_2} K (@Field.toSemifield.{u_2} K inst)))
      (@AddCommGroup.toAddCommMonoid.{u_6} W inst_3)]
  [inst_5 : Fintype.{u_5} V] [inst_6 : Fintype.{u_6} W] [inst_7 : DecidableEq.{u_6 + 1} W]
  (f :
    @LinearMap.{u_2, u_2, u_5, u_6} K K
      (@DivisionSemiring.toSemiring.{u_2} K (@Semifield.toDivisionSemiring.{u_2} K (@Field.toSemifield.{u_2} K inst)))
      (@DivisionSemiring.toSemiring.{u_2} K (@Semifield.toDivisionSemiring.{u_2} K (@Field.toSemifield.{u_2} K inst)))
      (@RingHom.id.{u_2} K
        (@Semiring.toNonAssocSemiring.{u_2} K
          (@DivisionSemiring.toSemiring.{u_2} K
            (@Semifield.toDivisionSemiring.{u_2} K (@Field.toSemifield.{u_2} K inst)))))
      V W (@AddCommGroup.toAddCommMonoid.{u_5} V inst_1) (@AddCommGroup.toAddCommMonoid.{u_6} W inst_3) inst_2 inst_4)
  (hf :
    @Function.Surjective.{u_5 + 1, u_6 + 1} V W
      (@DFunLike.coe.{max (u_5 + 1) (u_6 + 1), u_5 + 1, u_6 + 1}
        (@LinearMap.{u_2, u_2, u_5, u_6} K K
          (@DivisionSemiring.toSemiring.{u_2} K
            (@Semifield.toDivisionSemiring.{u_2} K (@Field.toSemifield.{u_2} K inst)))
          (@DivisionSemiring.toSemiring.{u_2} K
            (@Semifield.toDivisionSemiring.{u_2} K (@Field.toSemifield.{u_2} K inst)))
          (@RingHom.id.{u_2} K
            (@Semiring.toNonAssocSemiring.{u_2} K
              (@DivisionSemiring.toSemiring.{u_2} K
                (@Semifield.toDivisionSemiring.{u_2} K (@Field.toSemifield.{u_2} K inst)))))
          V W (@AddCommGroup.toAddCommMonoid.{u_5} V inst_1) (@AddCommGroup.toAddCommMonoid.{u_6} W inst_3) inst_2
          inst_4)
        V (fun (x : V) => W)
        (@LinearMap.instFunLike.{u_2, u_2, u_5, u_6} K K V W
          (@DivisionSemiring.toSemiring.{u_2} K
            (@Semifield.toDivisionSemiring.{u_2} K (@Field.toSemifield.{u_2} K inst)))
          (@DivisionSemiring.toSemiring.{u_2} K
            (@Semifield.toDivisionSemiring.{u_2} K (@Field.toSemifield.{u_2} K inst)))
          (@AddCommGroup.toAddCommMonoid.{u_5} V inst_1) (@AddCommGroup.toAddCommMonoid.{u_6} W inst_3) inst_2 inst_4
          (@RingHom.id.{u_2} K
            (@Semiring.toNonAssocSemiring.{u_2} K
              (@DivisionSemiring.toSemiring.{u_2} K
                (@Semifield.toDivisionSemiring.{u_2} K (@Field.toSemifield.{u_2} K inst))))))
        f))
  (target : W),
  @Eq.{1} Nat
    (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat) (@Fintype.card.{u_6} W inst_6)
      (@Finset.card.{u_5} V
        {x : V |
          @Eq.{u_6 + 1} W
            (@DFunLike.coe.{max (u_5 + 1) (u_6 + 1), u_5 + 1, u_6 + 1}
              (@LinearMap.{u_2, u_2, u_5, u_6} K K
                (@DivisionSemiring.toSemiring.{u_2} K
                  (@Semifield.toDivisionSemiring.{u_2} K (@Field.toSemifield.{u_2} K inst)))
                (@DivisionSemiring.toSemiring.{u_2} K
                  (@Semifield.toDivisionSemiring.{u_2} K (@Field.toSemifield.{u_2} K inst)))
                (@RingHom.id.{u_2} K
                  (@Semiring.toNonAssocSemiring.{u_2} K
                    (@DivisionSemiring.toSemiring.{u_2} K
                      (@Semifield.toDivisionSemiring.{u_2} K (@Field.toSemifield.{u_2} K inst)))))
                V W (@AddCommGroup.toAddCommMonoid.{u_5} V inst_1) (@AddCommGroup.toAddCommMonoid.{u_6} W inst_3) inst_2
                inst_4)
              V (fun (x : V) => W)
              (@LinearMap.instFunLike.{u_2, u_2, u_5, u_6} K K V W
                (@DivisionSemiring.toSemiring.{u_2} K
                  (@Semifield.toDivisionSemiring.{u_2} K (@Field.toSemifield.{u_2} K inst)))
                (@DivisionSemiring.toSemiring.{u_2} K
                  (@Semifield.toDivisionSemiring.{u_2} K (@Field.toSemifield.{u_2} K inst)))
                (@AddCommGroup.toAddCommMonoid.{u_5} V inst_1) (@AddCommGroup.toAddCommMonoid.{u_6} W inst_3) inst_2
                inst_4
                (@RingHom.id.{u_2} K
                  (@Semiring.toNonAssocSemiring.{u_2} K
                    (@DivisionSemiring.toSemiring.{u_2} K
                      (@Semifield.toDivisionSemiring.{u_2} K (@Field.toSemifield.{u_2} K inst))))))
              f x)
            target}))
    (@Fintype.card.{u_5} V inst_5) := by
  sorry
