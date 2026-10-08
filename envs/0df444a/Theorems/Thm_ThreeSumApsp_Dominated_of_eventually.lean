-- Prove2me | Theorems.Thm_ThreeSumApsp_Dominated_of_eventually
-- name    : ThreeSumApsp.Dominated.of_eventually
-- status  : Proved
-- author  : @wurtle
-- created : 2026-10-06T07:54:55.514977+00:00
-- url     : https://prove2.me/theorems/d4c18b0f-2bca-4c95-b7e6-849a8de774cb
-- title:
--   Extending an eventual upper bound to a positive tail
-- statement:
--   Let $f,g:\mathbb N\to\mathbb R$, let $C\in\mathbb R$, and suppose $f(n)\le Cg(n)$ for all sufficiently large $n$. If $g(n)>0$ for every $n\ge n_0$, then there exists $K\ge0$ such that
--
--   $$\forall n\ge n_0,\qquad f(n)\le K g(n).$$
--
--   This is domination on the specified tail. The finitely many values preceding the eventual bound are absorbed into a larger constant, allowing asymptotic estimates to serve as uniform bounds on the required domain.
--
--   References:
--
--   1. [Source formalization](https://github.com/anthropics/formal-math/blob/e1a4e6508154ea59f030480661590a9fe3018011/3sum-apsp/ThreeSumApsp/Util/Asymptotics/Dominated.lean#L248-L267).
-- source:
--   https://github.com/anthropics/formal-math/blob/e1a4e6508154ea59f030480661590a9fe3018011/3sum-apsp/ThreeSumApsp/Util/Asymptotics/Dominated.lean#L248-L267

/-
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0
-/

import Definitions.Def_APSPSource_ThreeSumApsp_Util_Asymptotics_Dominated
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Analysis.Asymptotics.Lemmas
import Mathlib.Analysis.Normed.Field.Basic
import Mathlib.Data.Real.Basic
import Mathlib.Order.Filter.AtTopBot.Basic

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option Elab.async false

theorem ThreeSumApsp.Dominated.of_eventually : ∀ {f g : Nat → Real} {C : Real},
  @Filter.Eventually.{0} Nat
      (fun (n : Nat) =>
        @LE.le.{0} Real Real.instLE (f n)
          (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul) C (g n)))
      (@Filter.atTop.{0} Nat Nat.instPreorder) →
    ∀ {n₀ : Nat},
      (∀ (n : Nat),
          @LE.le.{0} Nat instLENat n₀ n →
            @LT.lt.{0} Real Real.instLT (@OfNat.ofNat.{0} Real (nat_lit 0) (@Zero.toOfNat0.{0} Real Real.instZero))
              (g n)) →
        @ThreeSumApsp.Dominated.{0} Nat (fun (n : Nat) => @LE.le.{0} Nat instLENat n₀ n) f g := by
  sorry
