-- Prove2me | Theorems.Thm_ThreeSumApsp_Spec_chunkTab_cover
-- name    : ThreeSumApsp.Spec.chunkTab_cover
-- status  : Proved
-- author  : @wurtle
-- created : 2026-10-06T07:55:56.025146+00:00
-- url     : https://prove2.me/theorems/f77f3516-ae5f-4ce3-a5a1-ae9e547eb3fc
-- title:
--   Every matrix position belongs to a chunk
-- statement:
--   Let $n,p\in\mathbb N$, let $R_{AB}$ be a list of natural-number residue labels, and let the chunk capacity satisfy $\mathrm{cap}\ge1$. Suppose all label lookups at indices below $n^2$, using default zero, are less than $p$. Every position $j<n^2$ lies in a chunk of the source's chunk table:
--
--   $$\exists x\in\operatorname{chunkTab}(n,p,\mathrm{cap},R_{AB}),\qquad x.\operatorname{start}\le j<x.\operatorname{start}+x.\operatorname{len}.$$
--
--   This proves that the chunk partition used in Theorem 17 covers the entire sorted list of matrix-pair positions.
--
--   References:
--
--   1. [Source formalization](https://github.com/anthropics/formal-math/blob/e1a4e6508154ea59f030480661590a9fe3018011/3sum-apsp/ThreeSumApsp/Spec/Sec3/Theorem17/Chunks.lean#L229-L243).
-- source:
--   https://github.com/anthropics/formal-math/blob/e1a4e6508154ea59f030480661590a9fe3018011/3sum-apsp/ThreeSumApsp/Spec/Sec3/Theorem17/Chunks.lean#L229-L243

/-
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0
-/

import Definitions.Def_APSPSource_ThreeSumApsp_Spec_Sec3_Theorem17_Chunks
import Definitions.Def_APSPSource_ThreeSumApsp_Util_List
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Algebra.Order.BigOperators.Group.List
import Mathlib.Algebra.Order.BigOperators.Group.Multiset
import Mathlib.Algebra.Order.Floor.Div
import Mathlib.Algebra.Order.Group.Int
import Mathlib.Algebra.Order.Group.Nat
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Data.List.GetD
import Mathlib.Data.Nat.Count
import Mathlib.Data.Nat.Log

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option Elab.async false

theorem ThreeSumApsp.Spec.chunkTab_cover : ∀ {n p cap : Nat} {RAB : List.{0} Nat},
  @LE.le.{0} Nat instLENat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))) cap →
    (∀ (i : Nat),
        @LT.lt.{0} Nat instLTNat i (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat) n n) →
          @LT.lt.{0} Nat instLTNat
            (@List.getD.{0} Nat RAB i (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))) p) →
      ∀ {j : Nat},
        @LT.lt.{0} Nat instLTNat j (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat) n n) →
          ∃ (x : ThreeSumApsp.Spec.Chunk),
            And
              (@Membership.mem.{0, 0} ThreeSumApsp.Spec.Chunk (List.{0} ThreeSumApsp.Spec.Chunk)
                (@List.instMembership.{0} ThreeSumApsp.Spec.Chunk) (ThreeSumApsp.Spec.chunkTab n p cap RAB) x)
              (x.Contains j) := by
  sorry
