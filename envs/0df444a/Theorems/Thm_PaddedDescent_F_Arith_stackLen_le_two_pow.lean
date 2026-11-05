-- Prove2me | Theorems.Thm_PaddedDescent_F_Arith_stackLen_le_two_pow
-- name    : PaddedDescent.F.Arith.stackLen_le_two_pow
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T03:33:00.596134+00:00
-- url     : https://prove2.me/theorems/19a6f4ae-21b2-49a1-8061-5e94f113213b
-- title:
--   Arith: stack Len le two pow
-- statement:
--   With a = 2^z, n < a, bsum τ k ≤ a, 2^(k+1) ≤ a and 16 ≤ a: `stackLen k τ n (inLen k n)` ≤
--   a^(k+12).
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/PaddedDescent/F/ArithStack.lean#L102-L131
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/PaddedDescent/F/ArithStack.lean#L102-L131

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_PaddedDescent_F_Interfaces
import Definitions.Def_PaddedDescent_F_LenList
import Definitions.Def_PaddedDescent_Threshold
import Definitions.Def_SparsifyWidthK_Interfaces
import Definitions.Def_SparsifyWidthK_Thresholds
import Definitions.Def_PaddedDescent_F_ArithStack
set_option autoImplicit false
section
section
set_option exponentiation.threshold 1024
open PaddedDescent PaddedDescent.F PaddedDescent.F.Arith
open Groundwork Groundwork.Sparsify PaddedDescent.F.Lists
open WidthK (theta bsum)
open WidthK.Prog (stepK)

theorem PaddedDescent.F.Arith.stackLen_le_two_pow {k z n τ : ℕ} (hn : n < 2 ^ z) (hB : bsum τ k ≤ 2 ^ z) (hk : 2 ^ (k + 1) ≤ 2 ^ z) (h8 : 16 ≤ 2 ^ z) :
    stackLen k τ n (inLen k n) ≤ 2 ^ ((k + 12) * z) := by sorry
