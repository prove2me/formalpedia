-- Prove2me | Theorems.Thm_ThreeSumApsp_Theorem19_Choice_ceil_le_sqrt
-- name    : ThreeSumApsp.Theorem19.Choice.ceil_le_sqrt
-- status  : Proved
-- author  : @wurtle
-- created : 2026-10-06T08:22:43.898791+00:00
-- url     : https://prove2.me/theorems/f91fe613-0301-47c8-b6af-22daa26d70c7
-- title:
--   The rounded grouping parameter is at most the square root
-- statement:
--   Let $n,D\in\mathbb N$ and $\eta,c\in\mathbb R$ satisfy the source's parameter-choice conditions
--
--   $$16\le D,\qquad n^{1/18}/c\le D\le n^{1/18},\qquad c>0,\qquad 0\le\eta\le\tfrac14.$$
--
--   Then the grouping parameter $g=\lceil D^\eta\rceil$ satisfies $g\le\sqrt D$. This verifies the upper bound on $g$ needed to apply the reduction in Theorem 17 when proving Theorem 19.
--
--   References:
--
--   1. [Source formalization](https://github.com/anthropics/formal-math/blob/e1a4e6508154ea59f030480661590a9fe3018011/3sum-apsp/ThreeSumApsp/Sec3/Theorem19/Choice.lean#L99-L114).
-- source:
--   https://github.com/anthropics/formal-math/blob/e1a4e6508154ea59f030480661590a9fe3018011/3sum-apsp/ThreeSumApsp/Sec3/Theorem19/Choice.lean#L99-L114

/-
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0
-/

import Definitions.Def_APSPSource_ThreeSumApsp_Sec3_Theorem19_Choice
import Definitions.Def_TrulySubcubicAPSP_SourceSpecification
import Mathlib.Algebra.MvPolynomial.Basic
import Mathlib.Algebra.Order.Floor.Div
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Analysis.Complex.ExponentialBounds
import Mathlib.Analysis.SpecialFunctions.Log.Base
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Combinatorics.SimpleGraph.Basic
import Mathlib.Data.Finset.Sort
import Mathlib.Data.Nat.Log
import Mathlib.LinearAlgebra.Matrix.Notation
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.NumberTheory.PrimeCounting
import Mathlib.Probability.Independence.Basic
import Mathlib.Tactic.DeriveFintype

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option Elab.async false

theorem ThreeSumApsp.Theorem19.Choice.ceil_le_sqrt : ∀ {n D : Nat} {η c : Real},
  ThreeSumApsp.Theorem19.Choice n D η c →
    @LE.le.{0} Real Real.instLE
      (@Nat.cast.{0} Real Real.instNatCast
        (@Nat.ceil.{0} Real Real.semiring Real.partialOrder
          (@FloorRing.toFloorSemiring.{0} Real Real.instRing Real.linearOrder Real.instFloorRing)
          (@HPow.hPow.{0, 0, 0} Real Real Real (@instHPow.{0, 0} Real Real Real.instPow)
            (@Nat.cast.{0} Real Real.instNatCast D) η)))
      (@Nat.cast.{0} Real Real.instNatCast D).sqrt := by
  sorry
