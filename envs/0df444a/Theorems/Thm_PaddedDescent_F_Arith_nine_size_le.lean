-- Prove2me | Theorems.Thm_PaddedDescent_F_Arith_nine_size_le
-- name    : PaddedDescent.F.Arith.nine_size_le
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T03:31:58.817314+00:00
-- url     : https://prove2.me/theorems/6a43d712-9c1d-44f2-b732-bcf3b1f8ee2b
-- title:
--   Arith: nine size le
-- statement:
--   9·size n + 30 ≤ n/2^(sOf n) when sOf n ≥ 1.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/PaddedDescent/F/ArithStack.lean#L37-L41
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/PaddedDescent/F/ArithStack.lean#L37-L41

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

theorem PaddedDescent.F.Arith.nine_size_le {n : ℕ} (hs : 1 ≤ sOf n) : 9 * Nat.size n + 30 ≤ n / 2 ^ sOf n := by sorry
