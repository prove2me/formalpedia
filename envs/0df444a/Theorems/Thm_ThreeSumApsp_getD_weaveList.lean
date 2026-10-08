-- Prove2me | Theorems.Thm_ThreeSumApsp_getD_weaveList
-- name    : ThreeSumApsp.getD_weaveList
-- status  : Proved
-- author  : @wurtle
-- created : 2026-10-06T07:54:37.765173+00:00
-- url     : https://prove2.me/theorems/1e360732-4a48-40f0-8057-94e78697610c
-- title:
--   Indexed lookup in a mask-guided interleaving
-- statement:
--   Let $m$ be a Boolean mask, and let $A,B$ be lists of natural-number digits. The list $W=\operatorname{weaveList}(m,A,B)$ takes the next digit of $B$ at a true mask position and the next digit of $A$ at a false position, treating a missing digit as zero. For every natural index $\ell$, write $t_\ell$ and $f_\ell$ for the numbers of true and false entries in the first $\ell$ mask positions. Then
--
--   $$W[\ell]=\begin{cases}B[t_\ell],&\ell<|m|\text{ and }m[\ell]=1,\\A[f_\ell],&\ell<|m|\text{ and }m[\ell]=0,\\0,&\ell\ge|m|.\end{cases}$$
--
--   All list lookups use default zero. This relates the recursive interleaving implementation to its position-by-position specification.
--
--   References:
--
--   1. [Source formalization](https://github.com/anthropics/formal-math/blob/e1a4e6508154ea59f030480661590a9fe3018011/3sum-apsp/ThreeSumApsp/Util/Weave.lean#L40-L62).
-- source:
--   https://github.com/anthropics/formal-math/blob/e1a4e6508154ea59f030480661590a9fe3018011/3sum-apsp/ThreeSumApsp/Util/Weave.lean#L40-L62

/-
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0
-/

import Definitions.Def_APSPSource_ThreeSumApsp_Util_Weave
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Algebra.Order.BigOperators.Group.List
import Mathlib.Algebra.Order.BigOperators.Group.Multiset
import Mathlib.Algebra.Order.Group.Int
import Mathlib.Algebra.Order.Group.Nat
import Mathlib.Data.List.GetD
import Mathlib.Data.List.OfFn
import Mathlib.Data.Nat.Count
import Mathlib.Logic.Equiv.Basic
import Mathlib.Tactic.Ring

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option Elab.async false

theorem ThreeSumApsp.getD_weaveList : ∀ (mask : List.{0} Bool) (outer inner : List.{0} Nat) (ℓ : Nat),
  @Eq.{1} Nat
    (@List.getD.{0} Nat (ThreeSumApsp.weaveList mask outer inner) ℓ
      (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
    (@ite.{1} Nat (@LT.lt.{0} Nat instLTNat ℓ (@List.length.{0} Bool mask)) (ℓ.decLt (@List.length.{0} Bool mask))
      (@ite.{1} Nat (@Eq.{1} Bool (@List.getD.{0} Bool mask ℓ Bool.false) Bool.true)
        (instDecidableEqBool (@List.getD.{0} Bool mask ℓ Bool.false) Bool.true)
        (@List.getD.{0} Nat inner
          (@List.count.{0} Bool (@instBEqOfDecidableEq.{0} Bool instDecidableEqBool) Bool.true
            (@List.take.{0} Bool ℓ mask))
          (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
        (@List.getD.{0} Nat outer
          (@List.count.{0} Bool (@instBEqOfDecidableEq.{0} Bool instDecidableEqBool) Bool.false
            (@List.take.{0} Bool ℓ mask))
          (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))))
      (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))) := by
  sorry
