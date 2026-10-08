-- Prove2me | Theorems.Thm_ThreeSumApsp_Spec_length_nineStrs
-- name    : ThreeSumApsp.Spec.length_nineStrs
-- status  : Proved
-- author  : @wurtle
-- created : 2026-10-06T07:56:11.51687+00:00
-- url     : https://prove2.me/theorems/c9159fb2-11a3-4045-97f2-e386dbbe8d5b
-- title:
--   Counting strings with a bounded number of nines
-- statement:
--   For all natural numbers $n,\mathrm{lo},\mathrm{hi}$, the length of the source's bounded-nine enumeration is
--
--   $$\left|\operatorname{nineStrs}(n,\mathrm{lo},\mathrm{hi})\right|=\sum_{f=\mathrm{lo}}^{\mathrm{hi}}\binom nf9^{n-f}.$$
--
--   Each term counts strings with exactly $f$ digits equal to nine: choose their positions, then choose one of the other nine digits at each remaining position. Binomial coefficients vanish when $f>n$, and an empty interval contributes zero. This supplies the enumeration size used in the box-counting analysis.
--
--   References:
--
--   1. [Source formalization](https://github.com/anthropics/formal-math/blob/e1a4e6508154ea59f030480661590a9fe3018011/3sum-apsp/ThreeSumApsp/Spec/Sec4/Theorem30/NineStrings.lean#L198-L229).
-- source:
--   https://github.com/anthropics/formal-math/blob/e1a4e6508154ea59f030480661590a9fe3018011/3sum-apsp/ThreeSumApsp/Spec/Sec4/Theorem30/NineStrings.lean#L198-L229

/-
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0
-/

import Definitions.Def_APSPSource_ThreeSumApsp_Spec_Sec4_Theorem30_NineStrings
import Mathlib.Algebra.BigOperators.Intervals
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Data.List.Range
import Mathlib.Data.Nat.Choose.Basic
import Mathlib.Logic.Function.Iterate
import Mathlib.Order.Interval.Finset.Nat
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option Elab.async false

theorem ThreeSumApsp.Spec.length_nineStrs : ∀ (n lo hi : Nat),
  @Eq.{1} Nat (@List.length.{0} (List.{0} Nat) (ThreeSumApsp.Spec.nineStrs n lo hi))
    (∑ f ∈ @Finset.Icc.{0} Nat Nat.instPreorder Nat.instLocallyFiniteOrder lo hi,
      @HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat) (n.choose f)
        (@HPow.hPow.{0, 0, 0} Nat Nat Nat
          (@instHPow.{0, 0} Nat Nat (@NPow.toPow.{0} Nat (@Monoid.toNPow.{0} Nat Nat.instMonoid)))
          (@OfNat.ofNat.{0} Nat (nat_lit 9) (instOfNatNat (nat_lit 9)))
          (@HSub.hSub.{0, 0, 0} Nat Nat Nat (@instHSub.{0} Nat instSubNat) n f))) := by
  sorry
