-- Prove2me | Theorems.Thm_ThreeSum_HashFamily_hashMap_surjective
-- name    : ThreeSum.HashFamily.hashMap_surjective
-- status  : Open
-- author  : @wurtle
-- created : 2026-10-14T06:41:52.182845+00:00
-- url     : https://prove2.me/theorems/717ba377-2ba9-4999-8e06-8dd2c5755c28
-- title:
--   Independent coefficient rows make the hash map surjective
-- statement:
--   Let $K$ be a field, let $I$ and $S$ be finite sets, and let $(v_i)_{i\in I}$ be a linearly independent family in $K^S$. The hash map sends a weight vector $w\in K^S$ to the vector whose $i$th entry is $\sum_{x\in S}v_i(x)w(x)$. Every target vector is attained:
--
--   $$
--   \forall t\in K^I,\ \exists w\in K^S,\ \forall i\in I,
--   \qquad \sum_{x\in S}v_i(x)w(x)=t(i).
--   $$
--
--   The field itself need not be finite.
--
--   This proves that the concrete coefficient construction can realize all prescribed hash outputs, providing the linear-algebraic input for the later exact fiber counts.
-- source:
--   https://github.com/c0ldzy17/three-sum-lean/blob/2b639655e07421b9ac743de9090459bab473a7c0/Submission/ThreeSum/HashFamily.lean#L155-L172

import Definitions.Def_ThreeSum1962Source_Bundle01
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

universe u_2 u_3 u_4

theorem ThreeSum.HashFamily.hashMap_surjective : ∀ {K : Type u_2} {σ : Type u_3} {ι : Type u_4} [inst : Fintype.{u_3} σ] [Fintype.{u_4} ι] [inst_2 : Field.{u_2} K]
  {v : ι → σ → K}
  (hv :
    @LinearIndependent.{u_4, u_2, max u_2 u_3} ι K (σ → K) v
      (@DivisionSemiring.toSemiring.{u_2} K (@Semifield.toDivisionSemiring.{u_2} K (@Field.toSemifield.{u_2} K inst_2)))
      (@Pi.addCommMonoid.{u_3, u_2} σ (fun (a : σ) => K) fun (i : σ) =>
        @Semiring.toAddCommMonoid.{u_2} K
          (@DivisionSemiring.toSemiring.{u_2} K
            (@Semifield.toDivisionSemiring.{u_2} K (@Field.toSemifield.{u_2} K inst_2))))
      (@Pi.Function.module.{u_3, u_2, u_2} σ K K
        (@DivisionSemiring.toSemiring.{u_2} K
          (@Semifield.toDivisionSemiring.{u_2} K (@Field.toSemifield.{u_2} K inst_2)))
        (@Semiring.toAddCommMonoid.{u_2} K
          (@DivisionSemiring.toSemiring.{u_2} K
            (@Semifield.toDivisionSemiring.{u_2} K (@Field.toSemifield.{u_2} K inst_2))))
        (@Semiring.toModule.{u_2} K
          (@DivisionSemiring.toSemiring.{u_2} K
            (@Semifield.toDivisionSemiring.{u_2} K (@Field.toSemifield.{u_2} K inst_2)))))),
  @Function.Surjective.{max (u_2 + 1) (u_3 + 1), max (u_2 + 1) (u_4 + 1)} (σ → K) (ι → K)
    (@DFunLike.coe.{max (max (u_2 + 1) (u_3 + 1)) (u_4 + 1), max (u_2 + 1) (u_3 + 1), max (u_2 + 1) (u_4 + 1)}
      (@LinearMap.{u_2, u_2, max u_2 u_3, max u_2 u_4} K K
        (@DivisionSemiring.toSemiring.{u_2} K
          (@Semifield.toDivisionSemiring.{u_2} K (@Field.toSemifield.{u_2} K inst_2)))
        (@DivisionSemiring.toSemiring.{u_2} K
          (@Semifield.toDivisionSemiring.{u_2} K (@Field.toSemifield.{u_2} K inst_2)))
        (@RingHom.id.{u_2} K
          (@Semiring.toNonAssocSemiring.{u_2} K
            (@DivisionSemiring.toSemiring.{u_2} K
              (@Semifield.toDivisionSemiring.{u_2} K (@Field.toSemifield.{u_2} K inst_2)))))
        (σ → K) (ι → K)
        (@Pi.addCommMonoid.{u_3, u_2} σ (fun (a : σ) => K) fun (i : σ) =>
          @Semiring.toAddCommMonoid.{u_2} K
            (@DivisionSemiring.toSemiring.{u_2} K
              (@Semifield.toDivisionSemiring.{u_2} K (@Field.toSemifield.{u_2} K inst_2))))
        (@Pi.addCommMonoid.{u_4, u_2} ι (fun (a : ι) => K) fun (i : ι) =>
          @Semiring.toAddCommMonoid.{u_2} K
            (@DivisionSemiring.toSemiring.{u_2} K
              (@Semifield.toDivisionSemiring.{u_2} K (@Field.toSemifield.{u_2} K inst_2))))
        (@Pi.Function.module.{u_3, u_2, u_2} σ K K
          (@DivisionSemiring.toSemiring.{u_2} K
            (@Semifield.toDivisionSemiring.{u_2} K (@Field.toSemifield.{u_2} K inst_2)))
          (@Semiring.toAddCommMonoid.{u_2} K
            (@DivisionSemiring.toSemiring.{u_2} K
              (@Semifield.toDivisionSemiring.{u_2} K (@Field.toSemifield.{u_2} K inst_2))))
          (@Semiring.toModule.{u_2} K
            (@DivisionSemiring.toSemiring.{u_2} K
              (@Semifield.toDivisionSemiring.{u_2} K (@Field.toSemifield.{u_2} K inst_2)))))
        (@Pi.Function.module.{u_4, u_2, u_2} ι K K
          (@DivisionSemiring.toSemiring.{u_2} K
            (@Semifield.toDivisionSemiring.{u_2} K (@Field.toSemifield.{u_2} K inst_2)))
          (@Semiring.toAddCommMonoid.{u_2} K
            (@DivisionSemiring.toSemiring.{u_2} K
              (@Semifield.toDivisionSemiring.{u_2} K (@Field.toSemifield.{u_2} K inst_2))))
          (@Semiring.toModule.{u_2} K
            (@DivisionSemiring.toSemiring.{u_2} K
              (@Semifield.toDivisionSemiring.{u_2} K (@Field.toSemifield.{u_2} K inst_2))))))
      (σ → K) (fun (x : σ → K) => ι → K)
      (@LinearMap.instFunLike.{u_2, u_2, max u_2 u_3, max u_2 u_4} K K (σ → K) (ι → K)
        (@DivisionSemiring.toSemiring.{u_2} K
          (@Semifield.toDivisionSemiring.{u_2} K (@Field.toSemifield.{u_2} K inst_2)))
        (@DivisionSemiring.toSemiring.{u_2} K
          (@Semifield.toDivisionSemiring.{u_2} K (@Field.toSemifield.{u_2} K inst_2)))
        (@Pi.addCommMonoid.{u_3, u_2} σ (fun (a : σ) => K) fun (i : σ) =>
          @Semiring.toAddCommMonoid.{u_2} K
            (@DivisionSemiring.toSemiring.{u_2} K
              (@Semifield.toDivisionSemiring.{u_2} K (@Field.toSemifield.{u_2} K inst_2))))
        (@Pi.addCommMonoid.{u_4, u_2} ι (fun (a : ι) => K) fun (i : ι) =>
          @Semiring.toAddCommMonoid.{u_2} K
            (@DivisionSemiring.toSemiring.{u_2} K
              (@Semifield.toDivisionSemiring.{u_2} K (@Field.toSemifield.{u_2} K inst_2))))
        (@Pi.Function.module.{u_3, u_2, u_2} σ K K
          (@DivisionSemiring.toSemiring.{u_2} K
            (@Semifield.toDivisionSemiring.{u_2} K (@Field.toSemifield.{u_2} K inst_2)))
          (@Semiring.toAddCommMonoid.{u_2} K
            (@DivisionSemiring.toSemiring.{u_2} K
              (@Semifield.toDivisionSemiring.{u_2} K (@Field.toSemifield.{u_2} K inst_2))))
          (@Semiring.toModule.{u_2} K
            (@DivisionSemiring.toSemiring.{u_2} K
              (@Semifield.toDivisionSemiring.{u_2} K (@Field.toSemifield.{u_2} K inst_2)))))
        (@Pi.Function.module.{u_4, u_2, u_2} ι K K
          (@DivisionSemiring.toSemiring.{u_2} K
            (@Semifield.toDivisionSemiring.{u_2} K (@Field.toSemifield.{u_2} K inst_2)))
          (@Semiring.toAddCommMonoid.{u_2} K
            (@DivisionSemiring.toSemiring.{u_2} K
              (@Semifield.toDivisionSemiring.{u_2} K (@Field.toSemifield.{u_2} K inst_2))))
          (@Semiring.toModule.{u_2} K
            (@DivisionSemiring.toSemiring.{u_2} K
              (@Semifield.toDivisionSemiring.{u_2} K (@Field.toSemifield.{u_2} K inst_2)))))
        (@RingHom.id.{u_2} K
          (@Semiring.toNonAssocSemiring.{u_2} K
            (@DivisionSemiring.toSemiring.{u_2} K
              (@Semifield.toDivisionSemiring.{u_2} K (@Field.toSemifield.{u_2} K inst_2))))))
      (@ThreeSum.HashFamily.hashMap.{u_2, u_3, u_4} K σ ι inst inst_2 v)) := by
  sorry
