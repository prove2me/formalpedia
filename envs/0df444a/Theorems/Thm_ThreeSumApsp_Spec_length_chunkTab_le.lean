-- Prove2me | Theorems.Thm_ThreeSumApsp_Spec_length_chunkTab_le
-- name    : ThreeSumApsp.Spec.length_chunkTab_le
-- status  : Proved
-- author  : @wurtle
-- created : 2026-10-06T07:54:51.6309+00:00
-- url     : https://prove2.me/theorems/016d4b31-e267-4e9c-a171-f049e7ac5640
-- title:
--   Bounding the number of chunks in the matrix partition
-- statement:
--   Let $n,p\in\mathbb N$, let $R_{AB}$ be a list of natural-number residue labels, and suppose $\mathrm{cap}\ge1$. Assume each of the first $n^2$ label lookups, with default zero, is less than $p$. Then the source's chunk table satisfies
--
--   $$\left|\operatorname{chunkTab}(n,p,\mathrm{cap},R_{AB})\right|\le p+\left\lfloor\frac{n^2}{\mathrm{cap}}\right\rfloor.$$
--
--   This is the chunk-count estimate used in the proof of Theorem 17. Each residue class incurs at most one partially filled chunk, while the remaining chunks are charged to their capacity.
--
--   References:
--
--   1. [Source formalization](https://github.com/anthropics/formal-math/blob/e1a4e6508154ea59f030480661590a9fe3018011/3sum-apsp/ThreeSumApsp/Spec/Sec3/Theorem17/Chunks.lean#L266-L283).
-- source:
--   https://github.com/anthropics/formal-math/blob/e1a4e6508154ea59f030480661590a9fe3018011/3sum-apsp/ThreeSumApsp/Spec/Sec3/Theorem17/Chunks.lean#L266-L283

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

theorem ThreeSumApsp.Spec.length_chunkTab_le : ∀ {n p cap : Nat} {RAB : List.{0} Nat},
  @LE.le.{0} Nat instLENat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))) cap →
    (∀ (i : Nat),
        @LT.lt.{0} Nat instLTNat i (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat) n n) →
          @LT.lt.{0} Nat instLTNat
            (@List.getD.{0} Nat RAB i (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))) p) →
      @LE.le.{0} Nat instLENat (@List.length.{0} ThreeSumApsp.Spec.Chunk (ThreeSumApsp.Spec.chunkTab n p cap RAB))
        (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) p
          (@HDiv.hDiv.{0, 0, 0} Nat Nat Nat (@instHDiv.{0} Nat Nat.instDiv)
            (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat) n n) cap)) := by
  sorry
