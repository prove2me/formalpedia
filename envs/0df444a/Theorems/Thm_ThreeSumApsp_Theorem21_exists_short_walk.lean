-- Prove2me | Theorems.Thm_ThreeSumApsp_Theorem21_exists_short_walk
-- name    : ThreeSumApsp.Theorem21.exists_short_walk
-- status  : Proved
-- author  : @wurtle
-- created : 2026-10-06T07:51:34.642045+00:00
-- url     : https://prove2.me/theorems/8d405c0e-b05e-471e-87b7-5083861a8b24
-- title:
--   Removing closed pieces without increasing walk weight
-- statement:
--   Let $w$ be weights on $n$ vertices in $R\cup\{\infty\}$, where $R$ is a linearly ordered additive commutative group with order-preserving addition. Suppose every closed walk has nonnegative weight. Every walk $P$ has a walk $P'$ with the same initial and final vertices satisfying
--
--   $$|P'|<n,\qquad |P'|\le |P|,\qquad \operatorname{weight}_w(P')\le\operatorname{weight}_w(P).$$
--
--   A walk with at least $n$ edges repeats a vertex, so its intervening closed piece can be removed. Repeating this establishes the length bound needed to recover all shortest-path distances by repeated squaring.
--
--   References:
--
--   1. [Source formalization](https://github.com/anthropics/formal-math/blob/e1a4e6508154ea59f030480661590a9fe3018011/3sum-apsp/ThreeSumApsp/Sec3/Theorem21b/RepeatedSquaring.lean#L93-L116).
-- source:
--   https://github.com/anthropics/formal-math/blob/e1a4e6508154ea59f030480661590a9fe3018011/3sum-apsp/ThreeSumApsp/Sec3/Theorem21b/RepeatedSquaring.lean#L93-L116

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

theorem ThreeSumApsp.Theorem21.exists_short_walk : ∀ {R : Type} [inst : AddCommGroup.{0} R] [inst_1 : LinearOrder.{0} R]
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
    ∀ (i : Fin n) (rest : List.{0} (Fin n)),
      ∃ (rest' : List.{0} (Fin n)),
        And (@Eq.{1} (Fin n) (@ThreeSumApsp.walkEnd n i rest') (@ThreeSumApsp.walkEnd n i rest))
          (And (@LT.lt.{0} Nat instLTNat (@List.length.{0} (Fin n) rest') n)
            (And (@LE.le.{0} Nat instLENat (@List.length.{0} (Fin n) rest') (@List.length.{0} (Fin n) rest))
              (@LE.le.{0} (WithTop.{0} R)
                (@Preorder.toLE.{0} (WithTop.{0} R)
                  (@WithTop.instPreorder.{0} R
                    (@PartialOrder.toPreorder.{0} R
                      (@SemilatticeInf.toPartialOrder.{0} R
                        (@Lattice.toSemilatticeInf.{0} R
                          (@DistribLattice.toLattice.{0} R (@instDistribLatticeOfLinearOrder.{0} R inst_1)))))))
                (@ThreeSumApsp.walkWeight R
                  (@AddCommMagma.toAdd.{0} R
                    (@AddCommSemigroup.toAddCommMagma.{0} R
                      (@AddCommMonoid.toAddCommSemigroup.{0} R (@AddCommGroup.toAddCommMonoid.{0} R inst))))
                  (@NegZeroClass.toZero.{0} R
                    (@SubNegZeroMonoid.toNegZeroClass.{0} R
                      (@SubtractionMonoid.toSubNegZeroMonoid.{0} R
                        (@SubtractionCommMonoid.toSubtractionMonoid.{0} R
                          (@AddCommGroup.toDivisionAddCommMonoid.{0} R inst)))))
                  n w i rest')
                (@ThreeSumApsp.walkWeight R
                  (@AddCommMagma.toAdd.{0} R
                    (@AddCommSemigroup.toAddCommMagma.{0} R
                      (@AddCommMonoid.toAddCommSemigroup.{0} R (@AddCommGroup.toAddCommMonoid.{0} R inst))))
                  (@NegZeroClass.toZero.{0} R
                    (@SubNegZeroMonoid.toNegZeroClass.{0} R
                      (@SubtractionMonoid.toSubNegZeroMonoid.{0} R
                        (@SubtractionCommMonoid.toSubtractionMonoid.{0} R
                          (@AddCommGroup.toDivisionAddCommMonoid.{0} R inst)))))
                  n w i rest)))) := by
  sorry
