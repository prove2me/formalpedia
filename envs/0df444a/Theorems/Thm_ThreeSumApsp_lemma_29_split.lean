-- Prove2me | Theorems.Thm_ThreeSumApsp_lemma_29_split
-- name    : ThreeSumApsp.lemma_29_split
-- status  : Proved
-- author  : @wurtle
-- created : 2026-10-06T07:54:14.665186+00:00
-- url     : https://prove2.me/theorems/b740e015-2040-4492-ab8c-eb4ee9582bf2
-- title:
--   Replacing the highest star preserves the box condition
-- statement:
--   Fix natural numbers $L,m,t,e$. A box is a string of $L$ terms and stars with at most $m-t$ positions occupied by a star or the distinguished term $P_0$, and every star lies below every $P_0$. If a box $\pi$ has exactly $e+1$ stars, let $\ell$ be its highest star position. For every term $\lambda$,
--
--   $$\pi[\ell\leftarrow\lambda]\in\operatorname{Boxes}_{L,m,t}(e).$$
--
--   Here the right-hand set consists of boxes with exactly $e$ stars. This is the closure property used by the value-computation recurrence in Lemma 29.
--
--   References:
--
--   1. [Source formalization](https://github.com/anthropics/formal-math/blob/e1a4e6508154ea59f030480661590a9fe3018011/3sum-apsp/ThreeSumApsp/Sec4/Lemma29.lean#L139-L158).
-- source:
--   https://github.com/anthropics/formal-math/blob/e1a4e6508154ea59f030480661590a9fe3018011/3sum-apsp/ThreeSumApsp/Sec4/Lemma29.lean#L139-L158

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

theorem ThreeSumApsp.lemma_29_split : ∀ {L m t e : Nat} {π : ThreeSumApsp.Cube L},
  @Membership.mem.{0, 0} (ThreeSumApsp.Cube L) (Finset.{0} (ThreeSumApsp.Cube L))
      (@SetLike.instMembership.{0, 0} (Finset.{0} (ThreeSumApsp.Cube L)) (ThreeSumApsp.Cube L)
        (@Finset.instSetLike.{0} (ThreeSumApsp.Cube L)))
      (ThreeSumApsp.boxesWithStars L m t
        (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) e
          (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
      π →
    ∀ (hne : @Finset.Nonempty.{0} (Fin L) (@ThreeSumApsp.Cube.starLevels L π)) (lam : ThreeSumApsp.Term),
      @Membership.mem.{0, 0} (ThreeSumApsp.Cube L) (Finset.{0} (ThreeSumApsp.Cube L))
        (@SetLike.instMembership.{0, 0} (Finset.{0} (ThreeSumApsp.Cube L)) (ThreeSumApsp.Cube L)
          (@Finset.instSetLike.{0} (ThreeSumApsp.Cube L)))
        (ThreeSumApsp.boxesWithStars L m t e)
        (@ThreeSumApsp.Cube.replace L π
          (@Finset.max'.{0} (Fin L) (@Fin.instLinearOrder L) (@ThreeSumApsp.Cube.starLevels L π) hne) lam) := by
  sorry
