-- Prove2me | Theorems.Thm_ThreeSumApsp_log_mem
-- name    : ThreeSumApsp.log_mem
-- status  : Proved
-- author  : @wurtle
-- created : 2026-10-06T08:23:03.059873+00:00
-- url     : https://prove2.me/theorems/cc3dd7ca-3d31-46a1-b792-01d07fdf8b77
-- title:
--   A certified finite-series enclosure of the natural logarithm
-- statement:
--   Let $\theta>0$, $k\in\mathbb Z$, and $n\in\mathbb N$. Put $a=0.6931471803$, $b=0.6931471808$, and $x=(\theta-2^k)/(\theta+2^k)$. Define
--
--   $$A=k\frac{a+b}{2}+2\sum_{i=0}^{n-1}\frac{x^{2i+1}}{2i+1},\qquad
--   E=|k|\frac{b-a}{2}+\frac{2x^{2n}}{1-x^2}.$$
--
--   Then $\log\theta\in[A-E,A+E]$. The terminating decimals are exact rationals bounding $\log2$. The result holds for every $k,n$; choosing $2^k$ near $\theta$ and increasing $n$ improves the enclosure. This supplies certified numerical logarithm bounds for Table 2.
--
--   References:
--
--   1. [Source formalization](https://github.com/anthropics/formal-math/blob/e1a4e6508154ea59f030480661590a9fe3018011/3sum-apsp/ThreeSumApsp/Sec4/Table2/LogBounds.lean#L76-L106).
-- source:
--   https://github.com/anthropics/formal-math/blob/e1a4e6508154ea59f030480661590a9fe3018011/3sum-apsp/ThreeSumApsp/Sec4/Table2/LogBounds.lean#L76-L106

/-
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0
-/

import Definitions.Def_APSPSource_ThreeSumApsp_Sec4_Table2_LogBounds
import Definitions.Def_TrulySubcubicAPSP_SourceSpecification
import Mathlib.Algebra.MvPolynomial.Basic
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Algebra.Order.Field.Basic
import Mathlib.Algebra.Order.Ring.Abs
import Mathlib.Algebra.Order.Ring.Int
import Mathlib.Analysis.Complex.Exponential
import Mathlib.Analysis.Complex.ExponentialBounds
import Mathlib.Analysis.SpecialFunctions.BinaryEntropy
import Mathlib.Analysis.SpecialFunctions.Log.Base
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Combinatorics.SimpleGraph.Basic
import Mathlib.Data.Finset.Sort
import Mathlib.Data.Int.Cast.Lemmas
import Mathlib.Data.Nat.Cast.Order.Ring
import Mathlib.Data.Nat.Choose.Bounds
import Mathlib.Data.Nat.Choose.Sum
import Mathlib.LinearAlgebra.Matrix.Notation
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.NumberTheory.PrimeCounting
import Mathlib.Probability.Independence.Basic
import Mathlib.Tactic.DeriveFintype
import Mathlib.Tactic.GCongr
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option Elab.async false

theorem ThreeSumApsp.log_mem : ∀ (k : Int) (n : Nat) {θ : Real},
  @LT.lt.{0} Real Real.instLT (@OfNat.ofNat.{0} Real (nat_lit 0) (@Zero.toOfNat0.{0} Real Real.instZero)) θ →
    @Membership.mem.{0, 0} Real (Set.{0} Real) (@Set.instMembership.{0} Real)
      (@Set.Icc.{0} Real Real.instPreorder
        (@HSub.hSub.{0, 0, 0} Real Real Real (@instHSub.{0} Real Real.instSub) (ThreeSumApsp.logApprox k n θ)
          (ThreeSumApsp.logErr k n θ))
        (@HAdd.hAdd.{0, 0, 0} Real Real Real (@instHAdd.{0} Real Real.instAdd) (ThreeSumApsp.logApprox k n θ)
          (ThreeSumApsp.logErr k n θ)))
      (Real.log θ) := by
  sorry
