-- Prove2me | Theorems.Thm_ThreeSumApsp_Theorem21_exists_walk_of_entry
-- name    : ThreeSumApsp.Theorem21.exists_walk_of_entry
-- status  : Proved
-- author  : @wurtle
-- created : 2026-10-06T07:51:32.361046+00:00
-- url     : https://prove2.me/theorems/31a65f71-8e87-46c3-962e-54d360b442c4
-- title:
--   Every repeated-squaring entry is attained by a bounded-length walk
-- statement:
--   Let $R$ be an additive commutative group equipped with a linear order, and let $w$ assign weights in $R\cup\{\infty\}$ to ordered pairs of $n$ vertices. Define $M_0$ by replacing the diagonal of $w$ with zero, and set $M_{t+1}=M_t\otimes M_t$. For every $t\in\mathbb N$ and vertices $i,j$, there is a walk $P$ from $i$ to $j$ such that
--
--   $$|P|\le2^t,\qquad \operatorname{weight}_w(P)=M_t(i,j).$$
--
--   Here a walk is a vertex list, and its weight is $\infty$ if it uses a missing edge. No nonnegative-cycle hypothesis is needed. This supplies a witness for each entry in the repeated-squaring construction.
--
--   References:
--
--   1. [Source formalization](https://github.com/anthropics/formal-math/blob/e1a4e6508154ea59f030480661590a9fe3018011/3sum-apsp/ThreeSumApsp/Sec3/Theorem21b/RepeatedSquaring.lean#L46-L68).
-- source:
--   https://github.com/anthropics/formal-math/blob/e1a4e6508154ea59f030480661590a9fe3018011/3sum-apsp/ThreeSumApsp/Sec3/Theorem21b/RepeatedSquaring.lean#L46-L68

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

theorem ThreeSumApsp.Theorem21.exists_walk_of_entry : ∀ {R : Type} [inst : AddCommGroup.{0} R] [inst_1 : LinearOrder.{0} R] {n : Nat} (w : Fin n → Fin n → WithTop.{0} R)
  (t : Nat) (i j : Fin n),
  ∃ (rest : List.{0} (Fin n)),
    And (@Eq.{1} (Fin n) (@ThreeSumApsp.walkEnd n i rest) j)
      (And
        (@LE.le.{0} Nat instLENat (@List.length.{0} (Fin n) rest)
          (@HPow.hPow.{0, 0, 0} Nat Nat Nat
            (@instHPow.{0, 0} Nat Nat (@NPow.toPow.{0} Nat (@Monoid.toNPow.{0} Nat Nat.instMonoid)))
            (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))) t))
        (@Eq.{1} (WithTop.{0} R)
          (@ThreeSumApsp.walkWeight R
            (@AddCommMagma.toAdd.{0} R
              (@AddCommSemigroup.toAddCommMagma.{0} R
                (@AddCommMonoid.toAddCommSemigroup.{0} R (@AddCommGroup.toAddCommMonoid.{0} R inst))))
            (@NegZeroClass.toZero.{0} R
              (@SubNegZeroMonoid.toNegZeroClass.{0} R
                (@SubtractionMonoid.toSubNegZeroMonoid.{0} R
                  (@SubtractionCommMonoid.toSubtractionMonoid.{0} R
                    (@AddCommGroup.toDivisionAddCommMonoid.{0} R inst)))))
            n w i rest)
          (@ThreeSumApsp.minPlusSquares R
            (@AddCommMagma.toAdd.{0} R
              (@AddCommSemigroup.toAddCommMagma.{0} R
                (@AddCommMonoid.toAddCommSemigroup.{0} R (@AddCommGroup.toAddCommMonoid.{0} R inst))))
            (@NegZeroClass.toZero.{0} R
              (@SubNegZeroMonoid.toNegZeroClass.{0} R
                (@SubtractionMonoid.toSubNegZeroMonoid.{0} R
                  (@SubtractionCommMonoid.toSubtractionMonoid.{0} R
                    (@AddCommGroup.toDivisionAddCommMonoid.{0} R inst)))))
            inst_1 n w t i j))) := by
  sorry
