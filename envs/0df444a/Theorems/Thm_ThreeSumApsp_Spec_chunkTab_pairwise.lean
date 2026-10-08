-- Prove2me | Theorems.Thm_ThreeSumApsp_Spec_chunkTab_pairwise
-- name    : ThreeSumApsp.Spec.chunkTab_pairwise
-- status  : Proved
-- author  : @wurtle
-- created : 2026-10-06T07:54:41.320473+00:00
-- url     : https://prove2.me/theorems/a567ae57-68c7-4554-9baf-a306a65f3075
-- title:
--   Successive chunks occupy disjoint ordered intervals
-- statement:
--   Let $n,p\in\mathbb N$, let $R_{AB}$ be a list of natural-number residue labels, and let the natural chunk capacity satisfy $\mathrm{cap}\ge1$. Consider the source's chunk table $\operatorname{chunkTab}(n,p,\mathrm{cap},R_{AB})$. For any entry $x$ and any later entry $y$ in that list,
--
--   $$x.\operatorname{start}+x.\operatorname{len}\le y.\operatorname{start}.$$
--
--   The half-open intervals described by the chunks are therefore disjoint and ordered. This supports unique assignment of positions to chunks in the implementation of Theorem 17; no bound on the residue labels is needed for this ordering statement.
--
--   References:
--
--   1. [Source formalization](https://github.com/anthropics/formal-math/blob/e1a4e6508154ea59f030480661590a9fe3018011/3sum-apsp/ThreeSumApsp/Spec/Sec3/Theorem17/Chunks.lean#L206-L227).
-- source:
--   https://github.com/anthropics/formal-math/blob/e1a4e6508154ea59f030480661590a9fe3018011/3sum-apsp/ThreeSumApsp/Spec/Sec3/Theorem17/Chunks.lean#L206-L227

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

theorem ThreeSumApsp.Spec.chunkTab_pairwise : ∀ {n p cap : Nat} {RAB : List.{0} Nat},
  @LE.le.{0} Nat instLENat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))) cap →
    @List.Pairwise.{0} ThreeSumApsp.Spec.Chunk
      (fun (x y : ThreeSumApsp.Spec.Chunk) =>
        @LE.le.{0} Nat instLENat (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) x.start x.len)
          y.start)
      (ThreeSumApsp.Spec.chunkTab n p cap RAB) := by
  sorry
