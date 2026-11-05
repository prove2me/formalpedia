-- Prove2me | Theorems.Thm_PaddedDescent_F_Arith_inLen_le_pow
-- name    : PaddedDescent.F.Arith.inLen_le_pow
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T03:32:36.563613+00:00
-- url     : https://prove2.me/theorems/c244e2e0-bfcc-4ae5-b6f6-bda1f114f0b9
-- title:
--   Arith: in Len le pow
-- statement:
--   `inLen k n` ≤ a^(k+4) if n < a and 2^(k+1) ≤ a.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/PaddedDescent/F/ArithStack.lean#L83-L98
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/PaddedDescent/F/ArithStack.lean#L83-L98

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

theorem PaddedDescent.F.Arith.inLen_le_pow {k n a : ℕ} (hn : n < a) (hk : 2 ^ (k + 1) ≤ a) : inLen k n ≤ a ^ (k + 4) := by sorry
