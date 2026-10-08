-- Prove2me | Theorems.Thm_ThreeSumApsp_sec2_card_contributing_of_order
-- name    : ThreeSumApsp.sec2_card_contributing_of_order
-- status  : Proved
-- author  : @wurtle
-- created : 2026-10-06T07:54:26.365054+00:00
-- url     : https://prove2.me/theorems/4d9cffed-6480-4bc5-8578-69ea239aba4f
-- title:
--   Counting contributing leaves of each order
-- statement:
--   Let $w$ be an output string of length $L$ in the Section 2 encoding, and suppose its inner-position set has exactly $m$ elements. For every $d\in\mathbb N$, the number of leaves that contribute to $w$ and have order $d$ is
--
--   $$\#\{\tau:\tau\text{ contributes to }w,\ \operatorname{order}_m(\tau)=d\}=\binom md9^d.$$
--
--   The quantity on the right is $\alpha_d$. This supplies the exact order-by-order count in Section 2.4.3, which is later used to bound how many encoding entries a query reads.
--
--   References:
--
--   1. [Source formalization](https://github.com/anthropics/formal-math/blob/e1a4e6508154ea59f030480661590a9fe3018011/3sum-apsp/ThreeSumApsp/Sec2/Orders.lean#L140-L174).
-- source:
--   https://github.com/anthropics/formal-math/blob/e1a4e6508154ea59f030480661590a9fe3018011/3sum-apsp/ThreeSumApsp/Sec2/Orders.lean#L140-L174

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
import Mathlib.Algebra.Order.Field.Basic
import Mathlib.Algebra.Order.Ring.Rat
import Mathlib.Analysis.SpecialFunctions.Log.Base
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Combinatorics.SimpleGraph.Basic
import Mathlib.Data.Finset.Powerset
import Mathlib.Data.Finset.Sort
import Mathlib.Data.Fintype.BigOperators
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

theorem ThreeSumApsp.sec2_card_contributing_of_order : ∀ {L m : Nat} (w : ThreeSumApsp.OutStr L),
  @Eq.{1} Nat (@Finset.card.{0} (Fin L) (@ThreeSumApsp.innerSetO L w)) m →
    ∀ (d : Nat),
      @Eq.{1} Nat
        (@Finset.card.{0} (ThreeSumApsp.Leaf L)
          {τ : ThreeSumApsp.Leaf L |
            And (@ThreeSumApsp.Leaf.Contributes L τ w)
              (@Eq.{1} Int (@ThreeSumApsp.order L m τ) (@Nat.cast.{0} Int instNatCastInt d))})
        (ThreeSumApsp.alpha m d) := by
  sorry
