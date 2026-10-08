-- Prove2me | Theorems.Thm_ThreeSumApsp_goodTime_uniformTime
-- name    : ThreeSumApsp.goodTime_uniformTime
-- status  : Proved
-- author  : @wurtle
-- created : 2026-10-06T08:28:28.152796+00:00
-- url     : https://prove2.me/theorems/1ea5bb44-2125-47ec-b503-faf1ed9a8d2e
-- title:
--   The uniform Exact Triangle time satisfies the reduction requirements
-- statement:
--   Let $K,\delta\in\mathbb R$ with $K\ge1$ and $\delta\le1$, and let $e\in\mathbb N$. Write $\lambda(u)=\log(\max\{u,2\})$ and
--
--   $$T(s,u)=K s^{3-\delta}(\log s+1)^e(1+\lambda(u))^2.$$
--
--   For every real $u$ and integer $s\ge1$, this time bound satisfies
--
--   $$T(s,u)\ge s^2(1+\lambda(u)).$$
--
--   For fixed $u$, the quotient $T(s,u)/s$ is nondecreasing over integers $s\ge1$. These two properties are the source's `GoodTime` requirements for the reduction in Theorem 21(b). No lower bound on $\delta$ is assumed.
--
--   References:
--
--   1. [Source formalization](https://github.com/anthropics/formal-math/blob/e1a4e6508154ea59f030480661590a9fe3018011/3sum-apsp/ThreeSumApsp/TimeClaims/Sec3/Theorem21_22.lean#L200-L227).
-- source:
--   https://github.com/anthropics/formal-math/blob/e1a4e6508154ea59f030480661590a9fe3018011/3sum-apsp/ThreeSumApsp/TimeClaims/Sec3/Theorem21_22.lean#L200-L227

/-
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0
-/

import Definitions.Def_APSPSource_ThreeSumApsp_Sec3_Parameters
import Definitions.Def_APSPSource_ThreeSumApsp_Util_Log
import Definitions.Def_TrulySubcubicAPSP_SourceSpecification
import Mathlib.Algebra.BigOperators.GroupWithZero.Finset
import Mathlib.Algebra.Group.Action.Defs
import Mathlib.Algebra.MvPolynomial.Basic
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Algebra.Order.Field.Basic
import Mathlib.Algebra.Order.Floor.Div
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Ring.Abs
import Mathlib.Algebra.Order.Ring.Int
import Mathlib.Analysis.Asymptotics.Lemmas
import Mathlib.Analysis.Complex.ExponentialBounds
import Mathlib.Analysis.Normed.Field.Basic
import Mathlib.Analysis.SpecialFunctions.Log.Base
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Combinatorics.SimpleGraph.Basic
import Mathlib.Data.Finset.Powerset
import Mathlib.Data.Finset.Sort
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Data.Int.Cast.Lemmas
import Mathlib.Data.Nat.Cast.Order.Ring
import Mathlib.Data.Nat.Log
import Mathlib.Data.Real.Basic
import Mathlib.LinearAlgebra.Matrix.Notation
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.NumberTheory.PrimeCounting
import Mathlib.Order.Filter.AtTopBot.Basic
import Mathlib.Order.Interval.Finset.Fin
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

theorem ThreeSumApsp.goodTime_uniformTime : ∀ {K δ : Real} (e : Nat),
  @LE.le.{0} Real Real.instLE (@OfNat.ofNat.{0} Real (nat_lit 1) (@One.toOfNat1.{0} Real Real.instOne)) K →
    @LE.le.{0} Real Real.instLE δ (@OfNat.ofNat.{0} Real (nat_lit 1) (@One.toOfNat1.{0} Real Real.instOne)) →
      ThreeSumApsp.GoodTime (ThreeSumApsp.uniformTime K δ e) := by
  sorry
