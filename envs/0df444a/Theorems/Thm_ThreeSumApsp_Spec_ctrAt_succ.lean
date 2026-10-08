-- Prove2me | Theorems.Thm_ThreeSumApsp_Spec_ctrAt_succ
-- name    : ThreeSumApsp.Spec.ctrAt_succ
-- status  : Proved
-- author  : @wurtle
-- created : 2026-10-06T07:54:36.786357+00:00
-- url     : https://prove2.me/theorems/89494e97-566f-4b20-87f0-493743ec9753
-- title:
--   Incremental counters agree with the next row index
-- statement:
--   Let $k_0,n_0$ be positive natural numbers. For a row index $I$, define its band, block, and offset counters by
--
--   $$C(I)=\left(\left\lfloor\frac{I}{k_0n_0}\right\rfloor,\ \left\lfloor\frac I{n_0}\right\rfloor\bmod k_0,\ I\bmod n_0\right).$$
--
--   Let $\operatorname{step}$ increment the offset when possible, otherwise reset it and increment the block, and otherwise reset both and increment the band. Then
--
--   $$C(I+1)=\operatorname{step}(C(I)).$$
--
--   This justifies replacing repeated division by comparison-and-increment counters in the row traversal used by Theorem 5.
--
--   References:
--
--   1. [Source formalization](https://github.com/anthropics/formal-math/blob/e1a4e6508154ea59f030480661590a9fe3018011/3sum-apsp/ThreeSumApsp/Spec/Sec2/Theorem5/Counters.lean#L42-L59).
-- source:
--   https://github.com/anthropics/formal-math/blob/e1a4e6508154ea59f030480661590a9fe3018011/3sum-apsp/ThreeSumApsp/Spec/Sec2/Theorem5/Counters.lean#L42-L59

/-
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0
-/

import Definitions.Def_APSPSource_ThreeSumApsp_Spec_Sec2_Theorem5_Counters
import Definitions.Def_APSPSource_ThreeSumApsp_Util_Index
import Mathlib.Algebra.Order.Ring.Int

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option Elab.async false

theorem ThreeSumApsp.Spec.ctrAt_succ : ∀ {k₀ n₀ : Nat},
  @LT.lt.{0} Nat instLTNat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))) k₀ →
    @LT.lt.{0} Nat instLTNat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))) n₀ →
      ∀ (I : Nat),
        @Eq.{1} ThreeSumApsp.Spec.Ctr
          (ThreeSumApsp.Spec.ctrAt k₀ n₀
            (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) I
              (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
          (ThreeSumApsp.Spec.stepCtr k₀ n₀ (ThreeSumApsp.Spec.ctrAt k₀ n₀ I)) := by
  sorry
