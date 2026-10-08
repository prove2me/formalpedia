-- Prove2me | Theorems.Thm_ThreeSumApsp_Spec_bitLo_step
-- name    : ThreeSumApsp.Spec.bitLo_step
-- status  : Proved
-- author  : @wurtle
-- created : 2026-10-06T07:56:02.574991+00:00
-- url     : https://prove2.me/theorems/63591332-9c63-46d3-a3bf-daded6b05df6
-- title:
--   Recovering the next bit in the min-plus entry search
-- statement:
--   For integers $U,c$ with $c\ge-2U$ and a natural number $t$, define
--
--   $$B_t=-2U+2^t\left\lfloor\frac{c+2U}{2^t}\right\rfloor.$$
--
--   Thus $B_t$ clears the lowest $t$ bits of the nonnegative shifted value $c+2U$. Let $\chi(P)$ be $1$ when $P$ holds and $0$ otherwise. Then
--
--   $$B_t=B_{t+1}+2^t\bigl(1-\chi(c<B_{t+1}+2^t)\bigr).$$
--
--   One comparison therefore determines whether to add the next power of two. This is one round of the simultaneous binary search used to recover min-plus product entries.
--
--   References:
--
--   1. [Source formalization](https://github.com/anthropics/formal-math/blob/e1a4e6508154ea59f030480661590a9fe3018011/3sum-apsp/ThreeSumApsp/Spec/Sec3/Theorem21b/BitSearch.lean#L85-L104).
-- source:
--   https://github.com/anthropics/formal-math/blob/e1a4e6508154ea59f030480661590a9fe3018011/3sum-apsp/ThreeSumApsp/Spec/Sec3/Theorem21b/BitSearch.lean#L85-L104

/-
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0
-/

import Definitions.Def_APSPSource_ThreeSumApsp_Spec_Sec3_Theorem21b_BitSearch
import Definitions.Def_APSPSource_ThreeSumApsp_Util_Flag
import Definitions.Def_TrulySubcubicAPSP_SourceSpecification
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Algebra.MvPolynomial.Basic
import Mathlib.Algebra.Order.BigOperators.Group.List
import Mathlib.Algebra.Order.BigOperators.Group.Multiset
import Mathlib.Algebra.Order.Group.Int
import Mathlib.Algebra.Order.Group.Nat
import Mathlib.Algebra.Order.Ring.Int
import Mathlib.Analysis.SpecialFunctions.Log.Base
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Combinatorics.SimpleGraph.Basic
import Mathlib.Data.Finset.Sort
import Mathlib.Data.List.GetD
import Mathlib.Data.Nat.Count
import Mathlib.LinearAlgebra.Matrix.Notation
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.NumberTheory.PrimeCounting
import Mathlib.Probability.Independence.Basic
import Mathlib.Tactic.DeriveFintype

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option Elab.async false

theorem ThreeSumApsp.Spec.bitLo_step : ∀ {U c : Int},
  @LE.le.{0} Int Int.instLEInt
      (@Neg.neg.{0} Int Int.instNegInt
        (@HMul.hMul.{0, 0, 0} Int Int Int (@instHMul.{0} Int Int.instMul)
          (@OfNat.ofNat.{0} Int (nat_lit 2) (@instOfNat (nat_lit 2))) U))
      c →
    ∀ (t : Nat),
      @Eq.{1} Int (ThreeSumApsp.Spec.bitLo U t c)
        (@HAdd.hAdd.{0, 0, 0} Int Int Int (@instHAdd.{0} Int Int.instAdd)
          (ThreeSumApsp.Spec.bitLo U
            (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) t
              (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
            c)
          (@HMul.hMul.{0, 0, 0} Int Int Int (@instHMul.{0} Int Int.instMul)
            (@HPow.hPow.{0, 0, 0} Int Nat Int
              (@instHPow.{0, 0} Int Nat (@NPow.toPow.{0} Int (@Monoid.toNPow.{0} Int Int.instMonoid)))
              (@OfNat.ofNat.{0} Int (nat_lit 2) (@instOfNat (nat_lit 2))) t)
            (@HSub.hSub.{0, 0, 0} Int Int Int (@instHSub.{0} Int Int.instSub)
              (@OfNat.ofNat.{0} Int (nat_lit 1) (@instOfNat (nat_lit 1)))
              (ThreeSumApsp.flag
                (@LT.lt.{0} Int Int.instLTInt c
                  (@HAdd.hAdd.{0, 0, 0} Int Int Int (@instHAdd.{0} Int Int.instAdd)
                    (ThreeSumApsp.Spec.bitLo U
                      (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) t
                        (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
                      c)
                    (@HPow.hPow.{0, 0, 0} Int Nat Int
                      (@instHPow.{0, 0} Int Nat (@NPow.toPow.{0} Int (@Monoid.toNPow.{0} Int Int.instMonoid)))
                      (@OfNat.ofNat.{0} Int (nat_lit 2) (@instOfNat (nat_lit 2))) t))))))) := by
  sorry
