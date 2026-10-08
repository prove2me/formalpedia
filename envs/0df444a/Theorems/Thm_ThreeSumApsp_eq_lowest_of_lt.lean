-- Prove2me | Theorems.Thm_ThreeSumApsp_eq_lowest_of_lt
-- name    : ThreeSumApsp.eq_lowest_of_lt
-- status  : Proved
-- author  : @wurtle
-- created : 2026-10-06T07:51:17.296231+00:00
-- url     : https://prove2.me/theorems/fc6b2a7e-f4e6-4bb4-973a-c6b604b1d4bb
-- title:
--   Characterizing the lowest levels of a finite set
-- statement:
--   Let $L\in\mathbb N$ and let $T\subseteq S\subseteq\{0,\ldots,L-1\}$. Suppose every element of $T$ is smaller than every element of $S\setminus T$. Then
--
--   $$T=\operatorname{lowest}_{|T|}(S),$$
--
--   where $\operatorname{lowest}_k(S)$ consists of the elements of $S$ with fewer than $k$ elements of $S$ below them. This identifies the ordered subsets used to place stars in the box constructions of Section 4.2.
--
--   References:
--
--   1. [Source formalization](https://github.com/anthropics/formal-math/blob/e1a4e6508154ea59f030480661590a9fe3018011/3sum-apsp/ThreeSumApsp/Sec4/Boxes.lean#L332-L348).
-- source:
--   https://github.com/anthropics/formal-math/blob/e1a4e6508154ea59f030480661590a9fe3018011/3sum-apsp/ThreeSumApsp/Sec4/Boxes.lean#L332-L348

/-
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0
-/

import Definitions.Def_APSPSource_PaperStatements
import Definitions.Def_TrulySubcubicAPSP_SourceSpecification
import Mathlib.Algebra.BigOperators.GroupWithZero.Finset
import Mathlib.Algebra.Group.Action.Defs
import Mathlib.Algebra.MvPolynomial.Basic
import Mathlib.Algebra.MvPolynomial.CommRing
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Algebra.Order.Field.Basic
import Mathlib.Algebra.Order.Ring.Rat
import Mathlib.Analysis.Complex.Exponential
import Mathlib.Analysis.SpecialFunctions.Log.Base
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Combinatorics.SimpleGraph.Basic
import Mathlib.Data.Finset.Powerset
import Mathlib.Data.Finset.Sort
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Data.Nat.Choose.Bounds
import Mathlib.Data.Nat.Choose.Sum
import Mathlib.LinearAlgebra.Finsupp.LinearCombination
import Mathlib.LinearAlgebra.Matrix.Notation
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.NumberTheory.PrimeCounting
import Mathlib.Order.Interval.Finset.Fin
import Mathlib.Probability.Independence.Basic
import Mathlib.Tactic.DeriveFintype
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.NoncommRing
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option Elab.async false

theorem ThreeSumApsp.eq_lowest_of_lt : ∀ {L : Nat} {S T : Finset.{0} (Fin L)},
  @LE.le.{0} (Finset.{0} (Fin L))
      (@Preorder.toLE.{0} (Finset.{0} (Fin L))
        (@PartialOrder.toPreorder.{0} (Finset.{0} (Fin L)) (@Finset.instPartialOrder.{0} (Fin L))))
      T S →
    (∀ (ℓ : Fin L),
        @Membership.mem.{0, 0} (Fin L) (Finset.{0} (Fin L))
            (@SetLike.instMembership.{0, 0} (Finset.{0} (Fin L)) (Fin L) (@Finset.instSetLike.{0} (Fin L))) T ℓ →
          ∀ (ℓ' : Fin L),
            @Membership.mem.{0, 0} (Fin L) (Finset.{0} (Fin L))
                (@SetLike.instMembership.{0, 0} (Finset.{0} (Fin L)) (Fin L) (@Finset.instSetLike.{0} (Fin L)))
                (@SDiff.sdiff.{0} (Finset.{0} (Fin L)) (@Finset.instSDiff.{0} (Fin L) (instDecidableEqFin L)) S T) ℓ' →
              @LT.lt.{0} (Fin L) (@instLTFin L) ℓ ℓ') →
      @Eq.{1} (Finset.{0} (Fin L)) T (@ThreeSumApsp.lowest L (@Finset.card.{0} (Fin L) T) S) := by
  sorry
