-- Prove2me | Theorems.Thm_PaddedDescent_F_Arith_clause_word_le
-- name    : PaddedDescent.F.Arith.clause_word_le
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T01:44:19.015841+00:00
-- url     : https://prove2.me/theorems/f6015d61-c7bc-4310-857b-e039343fdc64
-- title:
--   Arith: clause word le
-- statement:
--   k·(3n + 5) + 10 ≤ a³ if n < a, k < a and 4 ≤ a.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/PaddedDescent/F/ArithStack.lean#L74-L80
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/PaddedDescent/F/ArithStack.lean#L74-L80

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

theorem PaddedDescent.F.Arith.clause_word_le {k n a : ℕ} (hn : n < a) (hk : k < a) (ha : 4 ≤ a) : k * (3 * n + 5) + 10 ≤ a ^ 3 := by sorry
