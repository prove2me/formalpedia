-- Prove2me | Theorems.Thm_ThreeSumApsp_Spec_pairwise_lt_nineStrs
-- name    : ThreeSumApsp.Spec.pairwise_lt_nineStrs
-- status  : Proved
-- author  : @wurtle
-- created : 2026-10-06T07:56:09.352462+00:00
-- url     : https://prove2.me/theorems/66a63824-a28a-4861-a13a-8c52342027b0
-- title:
--   Lexicographic order of the bounded-nine string enumeration
-- statement:
--   For natural numbers $n,\mathrm{lo},\mathrm{hi}$, the source's list $\operatorname{nineStrs}(n,\mathrm{lo},\mathrm{hi})$ enumerates length-$n$ strings over the digits $0,\ldots,9$ whose number of nines lies between the two bounds. The list is strictly increasing in lexicographic order:
--
--   $$i<j\quad\Longrightarrow\quad S_i<_{\mathrm{lex}}S_j.$$
--
--   Here $S$ denotes that list and $i,j$ are valid indices. This ordering property supports the deterministic traversal of the strings used to represent boxes and their components.
--
--   References:
--
--   1. [Source formalization](https://github.com/anthropics/formal-math/blob/e1a4e6508154ea59f030480661590a9fe3018011/3sum-apsp/ThreeSumApsp/Spec/Sec4/Theorem30/NineStrings.lean#L129-L154).
-- source:
--   https://github.com/anthropics/formal-math/blob/e1a4e6508154ea59f030480661590a9fe3018011/3sum-apsp/ThreeSumApsp/Spec/Sec4/Theorem30/NineStrings.lean#L129-L154

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

theorem ThreeSumApsp.Spec.pairwise_lt_nineStrs : ∀ (n lo hi : Nat),
  @List.Pairwise.{0} (List.{0} Nat)
    (fun (x1 x2 : List.{0} Nat) => @LT.lt.{0} (List.{0} Nat) (@List.instLT.{0} Nat instLTNat) x1 x2)
    (ThreeSumApsp.Spec.nineStrs n lo hi) := by
  sorry
