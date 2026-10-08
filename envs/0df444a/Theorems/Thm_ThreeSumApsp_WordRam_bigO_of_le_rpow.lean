-- Prove2me | Theorems.Thm_ThreeSumApsp_WordRam_bigO_of_le_rpow
-- name    : ThreeSumApsp.WordRam.bigO_of_le_rpow
-- status  : Proved
-- author  : @wurtle
-- created : 2026-10-06T07:47:34.815607+00:00
-- url     : https://prove2.me/theorems/08002359-8dc0-4af2-8a5d-0df9343970ca
-- title:
--   Converting a real power bound to the word-RAM time specification
-- statement:
--   Let $T:\mathbb N\to\mathbb N$, let $C\in\mathbb R$, and let $r\ge0$ be rational. Suppose $T(n)\le Cn^r$ for every integer $n\ge2$. Writing $r=p/q$ in reduced form with $p\ge0$ and $q>0$, there is a natural number $K$ such that
--
--   $$\forall n\ge2,\qquad T(n)^q\le K n^p.$$
--
--   This is precisely the integer-power definition of $T(n)=O(n^r)$ used in the source's final machine specification. It connects the real-valued asymptotic estimates in the analysis with the rational exponents in the formal running-time claims.
--
--   References:
--
--   1. [Source formalization](https://github.com/anthropics/formal-math/blob/e1a4e6508154ea59f030480661590a9fe3018011/3sum-apsp/ThreeSumApsp/Statements/Exponents.lean#L37-L50).
-- source:
--   https://github.com/anthropics/formal-math/blob/e1a4e6508154ea59f030480661590a9fe3018011/3sum-apsp/ThreeSumApsp/Statements/Exponents.lean#L37-L50

/-
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0
-/

import Definitions.Def_TrulySubcubicAPSP_SourceSpecification
import Mathlib.Algebra.MvPolynomial.Basic
import Mathlib.Algebra.Order.Field.Basic
import Mathlib.Algebra.Order.Ring.Abs
import Mathlib.Algebra.Order.Ring.Int
import Mathlib.Analysis.SpecialFunctions.Log.Base
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Combinatorics.SimpleGraph.Basic
import Mathlib.Data.Finset.Sort
import Mathlib.Data.Int.Cast.Lemmas
import Mathlib.Data.Nat.Cast.Order.Ring
import Mathlib.Data.Set.Function
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

theorem ThreeSumApsp.WordRam.bigO_of_le_rpow : ∀ {C : Real} {r : Rat},
  @LE.le.{0} Rat Rat.instLE (@OfNat.ofNat.{0} Rat (nat_lit 0) (@Rat.instOfNat (nat_lit 0))) r →
    ∀ {T : Nat → Nat},
      (∀ (n : Nat),
          @LE.le.{0} Nat instLENat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))) n →
            @LE.le.{0} Real Real.instLE (@Nat.cast.{0} Real Real.instNatCast (T n))
              (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul) C
                (@HPow.hPow.{0, 0, 0} Real Real Real (@instHPow.{0, 0} Real Real Real.instPow)
                  (@Nat.cast.{0} Real Real.instNatCast n) (@Rat.cast.{0} Real Real.instRatCast r)))) →
        EndStatement.BigO T r := by
  sorry
