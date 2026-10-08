-- Prove2me | Theorems.Thm_ThreeSumApsp_Theorem21_entry_le_walkWeight
-- name    : ThreeSumApsp.Theorem21.entry_le_walkWeight
-- status  : Proved
-- author  : @wurtle
-- created : 2026-10-06T07:51:44.662751+00:00
-- url     : https://prove2.me/theorems/9043d1e1-38f6-4c00-aad6-a6a684e299e6
-- title:
--   Repeated min-plus squaring bounds every sufficiently short walk
-- statement:
--   Let $R$ be a linearly ordered additive commutative group whose addition preserves order, and let $w$ be edge weights on $n$ vertices with values in $R\cup\{\infty\}$. Assume every closed walk has nonnegative weight. Set $M_0(i,i)=0$, $M_0(i,j)=w(i,j)$ for $i\ne j$, and $M_{t+1}=M_t\otimes M_t$ for the min-plus product. Every walk $P$ from $i$ to $j$ with at most $2^t$ edges satisfies
--
--   $$M_t(i,j)\le\operatorname{weight}_w(P).$$
--
--   Missing edges contribute $\infty$. This proves the lower-bound direction relating repeated squaring to shortest-path distances in Theorem 21(b).
--
--   References:
--
--   1. [Source formalization](https://github.com/anthropics/formal-math/blob/e1a4e6508154ea59f030480661590a9fe3018011/3sum-apsp/ThreeSumApsp/Sec3/Theorem21b/RepeatedSquaring.lean#L118-L151).
-- source:
--   https://github.com/anthropics/formal-math/blob/e1a4e6508154ea59f030480661590a9fe3018011/3sum-apsp/ThreeSumApsp/Sec3/Theorem21b/RepeatedSquaring.lean#L118-L151

/-
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0
-/

import Definitions.Def_APSPSource_PaperStatements
import Definitions.Def_TrulySubcubicAPSP_SourceSpecification
import Mathlib.Algebra.MvPolynomial.Basic
import Mathlib.Analysis.SpecialFunctions.Log.Base
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Combinatorics.SimpleGraph.Basic
import Mathlib.Data.Finset.Sort
import Mathlib.LinearAlgebra.Matrix.Notation
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.NumberTheory.PrimeCounting
import Mathlib.Probability.Independence.Basic
import Mathlib.Tactic.DeriveFintype

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option Elab.async false

theorem ThreeSumApsp.Theorem21.entry_le_walkWeight : ∀ {R : Type} [inst : AddCommGroup.{0} R] [inst_1 : LinearOrder.{0} R]
  [@IsOrderedAddMonoid.{0} R (@AddCommGroup.toAddCommMonoid.{0} R inst)
      (@PartialOrder.toPreorder.{0} R
        (@SemilatticeInf.toPartialOrder.{0} R
          (@Lattice.toSemilatticeInf.{0} R
            (@DistribLattice.toLattice.{0} R (@instDistribLatticeOfLinearOrder.{0} R inst_1)))))]
  {n : Nat} (w : Fin n → Fin n → WithTop.{0} R),
  @ThreeSumApsp.NoNegativeCycle R
      (@AddCommMagma.toAdd.{0} R
        (@AddCommSemigroup.toAddCommMagma.{0} R
          (@AddCommMonoid.toAddCommSemigroup.{0} R (@AddCommGroup.toAddCommMonoid.{0} R inst))))
      (@NegZeroClass.toZero.{0} R
        (@SubNegZeroMonoid.toNegZeroClass.{0} R
          (@SubtractionMonoid.toSubNegZeroMonoid.{0} R
            (@SubtractionCommMonoid.toSubtractionMonoid.{0} R (@AddCommGroup.toDivisionAddCommMonoid.{0} R inst)))))
      (@Preorder.toLE.{0} R
        (@PartialOrder.toPreorder.{0} R
          (@SemilatticeInf.toPartialOrder.{0} R
            (@Lattice.toSemilatticeInf.{0} R
              (@DistribLattice.toLattice.{0} R (@instDistribLatticeOfLinearOrder.{0} R inst_1))))))
      n w →
    ∀ (t : Nat) (i : Fin n) (rest : List.{0} (Fin n)),
      @LE.le.{0} Nat instLENat (@List.length.{0} (Fin n) rest)
          (@HPow.hPow.{0, 0, 0} Nat Nat Nat
            (@instHPow.{0, 0} Nat Nat (@NPow.toPow.{0} Nat (@Monoid.toNPow.{0} Nat Nat.instMonoid)))
            (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))) t) →
        @LE.le.{0} (WithTop.{0} R)
          (@Preorder.toLE.{0} (WithTop.{0} R)
            (@WithTop.instPreorder.{0} R
              (@PartialOrder.toPreorder.{0} R
                (@SemilatticeInf.toPartialOrder.{0} R
                  (@Lattice.toSemilatticeInf.{0} R
                    (@DistribLattice.toLattice.{0} R (@instDistribLatticeOfLinearOrder.{0} R inst_1)))))))
          (@ThreeSumApsp.minPlusSquares R
            (@AddCommMagma.toAdd.{0} R
              (@AddCommSemigroup.toAddCommMagma.{0} R
                (@AddCommMonoid.toAddCommSemigroup.{0} R (@AddCommGroup.toAddCommMonoid.{0} R inst))))
            (@NegZeroClass.toZero.{0} R
              (@SubNegZeroMonoid.toNegZeroClass.{0} R
                (@SubtractionMonoid.toSubNegZeroMonoid.{0} R
                  (@SubtractionCommMonoid.toSubtractionMonoid.{0} R
                    (@AddCommGroup.toDivisionAddCommMonoid.{0} R inst)))))
            inst_1 n w t i (@ThreeSumApsp.walkEnd n i rest))
          (@ThreeSumApsp.walkWeight R
            (@AddCommMagma.toAdd.{0} R
              (@AddCommSemigroup.toAddCommMagma.{0} R
                (@AddCommMonoid.toAddCommSemigroup.{0} R (@AddCommGroup.toAddCommMonoid.{0} R inst))))
            (@NegZeroClass.toZero.{0} R
              (@SubNegZeroMonoid.toNegZeroClass.{0} R
                (@SubtractionMonoid.toSubNegZeroMonoid.{0} R
                  (@SubtractionCommMonoid.toSubtractionMonoid.{0} R
                    (@AddCommGroup.toDivisionAddCommMonoid.{0} R inst)))))
            n w i rest) := by
  sorry
