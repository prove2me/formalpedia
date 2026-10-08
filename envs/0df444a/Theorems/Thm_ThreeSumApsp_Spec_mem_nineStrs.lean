-- Prove2me | Theorems.Thm_ThreeSumApsp_Spec_mem_nineStrs
-- name    : ThreeSumApsp.Spec.mem_nineStrs
-- status  : Proved
-- author  : @wurtle
-- created : 2026-10-06T07:56:16.90634+00:00
-- url     : https://prove2.me/theorems/d4f5408d-d8e0-4a71-b60e-4f505890100b
-- title:
--   Membership in the bounded-nine string enumeration
-- statement:
--   For natural numbers $n,\mathrm{lo},\mathrm{hi}$ and a list $s$ of natural-number digits, membership in the source enumeration is characterized exactly by
--
--   $$s\in\operatorname{nineStrs}(n,\mathrm{lo},\mathrm{hi})\iff |s|=n\ \land\ (\forall d\in s,\ d<10)\ \land\ \mathrm{lo}\le\#_9(s)\le\mathrm{hi},$$
--
--   where $\#_9(s)$ counts occurrences of the digit $9$. This proves that the recursive enumeration produces exactly the required strings, including when the bounds are inconsistent or exceed the string length.
--
--   References:
--
--   1. [Source formalization](https://github.com/anthropics/formal-math/blob/e1a4e6508154ea59f030480661590a9fe3018011/3sum-apsp/ThreeSumApsp/Spec/Sec4/Theorem30/NineStrings.lean#L94-L110).
-- source:
--   https://github.com/anthropics/formal-math/blob/e1a4e6508154ea59f030480661590a9fe3018011/3sum-apsp/ThreeSumApsp/Spec/Sec4/Theorem30/NineStrings.lean#L94-L110

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

theorem ThreeSumApsp.Spec.mem_nineStrs : ∀ {n lo hi : Nat} (l : List.{0} Nat),
  Iff
    (@Membership.mem.{0, 0} (List.{0} Nat) (List.{0} (List.{0} Nat)) (@List.instMembership.{0} (List.{0} Nat))
      (ThreeSumApsp.Spec.nineStrs n lo hi) l)
    (And (@Eq.{1} Nat (@List.length.{0} Nat l) n)
      (And
        (∀ (d : Nat),
          @Membership.mem.{0, 0} Nat (List.{0} Nat) (@List.instMembership.{0} Nat) l d →
            @LT.lt.{0} Nat instLTNat d (@OfNat.ofNat.{0} Nat (nat_lit 10) (instOfNatNat (nat_lit 10))))
        (And
          (@LE.le.{0} Nat instLENat lo
            (@List.count.{0} Nat (@instBEqOfDecidableEq.{0} Nat instDecidableEqNat)
              (@OfNat.ofNat.{0} Nat (nat_lit 9) (instOfNatNat (nat_lit 9))) l))
          (@LE.le.{0} Nat instLENat
            (@List.count.{0} Nat (@instBEqOfDecidableEq.{0} Nat instDecidableEqNat)
              (@OfNat.ofNat.{0} Nat (nat_lit 9) (instOfNatNat (nat_lit 9))) l)
            hi)))) := by
  sorry
