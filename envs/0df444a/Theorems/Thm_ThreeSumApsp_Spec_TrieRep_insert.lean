-- Prove2me | Theorems.Thm_ThreeSumApsp_Spec_TrieRep_insert
-- name    : ThreeSumApsp.Spec.TrieRep.insert
-- status  : Proved
-- author  : @wurtle
-- created : 2026-10-06T07:56:14.222801+00:00
-- url     : https://prove2.me/theorems/488175d5-2fe1-4a4d-9524-2a2e03c5ac4c
-- title:
--   Trie insertion preserves the representation invariant
-- statement:
--   Let an integer array $T$ represent a family of tries for length-$L$ strings over digits $0,\ldots,10$, with lower allocation boundary $\mathrm{lo}$, root-address function $r$, and recorded partial value table $f$. The representation requires distinct aligned eleven-cell vertices within the allocated array, consistent child pointers, and correct storage of every recorded value. If $r(i)\ne0$, $|s|=L$, every digit of $s$ is below $11$, and $v\in\mathbb Z$, then
--
--   $$\operatorname{TrieRep}\bigl(L,\mathrm{lo},\operatorname{insert}(T,r(i),s,v),r,f[(i,s)\mapsto\operatorname{some}(v)]\bigr).$$
--
--   Thus storing one key preserves the trie representation and all other recorded values. This is the insertion specification used for the box-value dictionaries in Section 4.3.
--
--   References:
--
--   1. [Source formalization](https://github.com/anthropics/formal-math/blob/e1a4e6508154ea59f030480661590a9fe3018011/3sum-apsp/ThreeSumApsp/Spec/Sec4/Theorem30/Trie.lean#L479-L499).
-- source:
--   https://github.com/anthropics/formal-math/blob/e1a4e6508154ea59f030480661590a9fe3018011/3sum-apsp/ThreeSumApsp/Spec/Sec4/Theorem30/Trie.lean#L479-L499

/-
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0
-/

import Definitions.Def_APSPSource_ThreeSumApsp_Spec_Sec4_Theorem30_Trie
import Mathlib.Data.Int.Notation
import Mathlib.Data.List.GetD
import Mathlib.Data.List.Induction
import Mathlib.Logic.Function.Basic
import Mathlib.Tactic.SplitIfs

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option Elab.async false

theorem ThreeSumApsp.Spec.TrieRep.insert : ∀ {L lo : Nat} {T : List.{0} Int} {roots : Nat → Nat} {f : Prod.{0, 0} Nat (List.{0} Nat) → Option.{0} Int},
  ThreeSumApsp.Spec.TrieRep L lo T roots f →
    ∀ (i : Nat),
      @Ne.{1} Nat (roots i) (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))) →
        ∀ (key : List.{0} Nat),
          @Eq.{1} Nat (@List.length.{0} Nat key) L →
            (∀ (d : Nat),
                @Membership.mem.{0, 0} Nat (List.{0} Nat) (@List.instMembership.{0} Nat) key d →
                  @LT.lt.{0} Nat instLTNat d (@OfNat.ofNat.{0} Nat (nat_lit 11) (instOfNatNat (nat_lit 11)))) →
              ∀ (v : Int),
                ThreeSumApsp.Spec.TrieRep L lo (ThreeSumApsp.Spec.trieInsert T (roots i) key v) roots
                  (@Function.update.{1, 1} (Prod.{0, 0} Nat (List.{0} Nat))
                    (fun (a : Prod.{0, 0} Nat (List.{0} Nat)) => Option.{0} Int)
                    (fun (a b : Prod.{0, 0} Nat (List.{0} Nat)) =>
                      @instDecidableEqProd.{0, 0} Nat (List.{0} Nat) instDecidableEqNat
                        (fun (a b : List.{0} Nat) => @instDecidableEqList.{0} Nat instDecidableEqNat a b) a b)
                    f (@Prod.mk.{0, 0} Nat (List.{0} Nat) i key) (@Option.some.{0} Int v)) := by
  sorry
