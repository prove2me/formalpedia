-- Prove2me | Theorems.Thm_ThreeSumApsp_pref_step
-- name    : ThreeSumApsp.pref_step
-- status  : Proved
-- author  : @wurtle
-- created : 2026-10-06T07:56:05.104716+00:00
-- url     : https://prove2.me/theorems/29fcf3a6-d134-4287-8f85-1e39ce9aa02d
-- title:
--   Updating a binary prefix and its shifted remainder
-- statement:
--   Let $L,\ell\in\mathbb N$ with $\ell+1\le L$, and let $z\in\mathbb Z$. Define the Euclidean quotient and shifted remainder
--
--   $$q_k=\left\lfloor\frac z{2^k}\right\rfloor,\qquad r_k=(z\bmod2^k)2^{L-k},\qquad P=2^L.$$
--
--   The next pair is obtained by doubling and one comparison:
--
--   $$ (q_\ell,r_\ell)=\begin{cases}(2q_{\ell+1},2r_{\ell+1}),&2r_{\ell+1}<P,\\(2q_{\ell+1}+1,2r_{\ell+1}-P),&2r_{\ell+1}\ge P.\end{cases}$$
--
--   The identity holds for every integer $z$. It justifies computing binary prefixes one bit at a time without division in the implementation.
--
--   References:
--
--   1. [Source formalization](https://github.com/anthropics/formal-math/blob/e1a4e6508154ea59f030480661590a9fe3018011/3sum-apsp/ThreeSumApsp/Util/BinaryPrefixes.lean#L50-L82).
-- source:
--   https://github.com/anthropics/formal-math/blob/e1a4e6508154ea59f030480661590a9fe3018011/3sum-apsp/ThreeSumApsp/Util/BinaryPrefixes.lean#L50-L82

/-
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0
-/

import Definitions.Def_APSPSource_ThreeSumApsp_Util_BinaryPrefixes
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Algebra.Order.BigOperators.Group.List
import Mathlib.Algebra.Order.BigOperators.Group.Multiset
import Mathlib.Algebra.Order.Group.Int
import Mathlib.Algebra.Order.Group.Nat
import Mathlib.Data.List.GetD
import Mathlib.Data.Nat.Count
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option Elab.async false

theorem ThreeSumApsp.pref_step : ∀ {L ℓ : Nat},
  @LE.le.{0} Nat instLENat
      (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) ℓ
        (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
      L →
    ∀ (z : Int),
      And
        (@Eq.{1} Int (ThreeSumApsp.prefQ ℓ z)
          (ThreeSumApsp.shiftQ
            (@HPow.hPow.{0, 0, 0} Int Nat Int
              (@instHPow.{0, 0} Int Nat (@NPow.toPow.{0} Int (@Monoid.toNPow.{0} Int Int.instMonoid)))
              (@OfNat.ofNat.{0} Int (nat_lit 2) (@instOfNat (nat_lit 2))) L)
            (ThreeSumApsp.prefQ
              (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) ℓ
                (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
              z)
            (ThreeSumApsp.prefR L
              (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) ℓ
                (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
              z)))
        (@Eq.{1} Int (ThreeSumApsp.prefR L ℓ z)
          (ThreeSumApsp.shiftR
            (@HPow.hPow.{0, 0, 0} Int Nat Int
              (@instHPow.{0, 0} Int Nat (@NPow.toPow.{0} Int (@Monoid.toNPow.{0} Int Int.instMonoid)))
              (@OfNat.ofNat.{0} Int (nat_lit 2) (@instOfNat (nat_lit 2))) L)
            (ThreeSumApsp.prefR L
              (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) ℓ
                (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
              z))) := by
  sorry
