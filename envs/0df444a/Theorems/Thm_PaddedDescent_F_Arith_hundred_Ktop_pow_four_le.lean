-- Prove2me | Theorems.Thm_PaddedDescent_F_Arith_hundred_Ktop_pow_four_le
-- name    : PaddedDescent.F.Arith.hundred_Ktop_pow_four_le
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T01:45:00.481256+00:00
-- url     : https://prove2.me/theorems/e2d9c5ac-ae7b-4da5-bafa-6b5941d28d2f
-- title:
--   Arith: hundred Ktop pow four le
-- statement:
--   100·K_t⁴ ≤ Y.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/PaddedDescent/F/ArithTopInv.lean#L51-L53
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/PaddedDescent/F/ArithTopInv.lean#L51-L53

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_PaddedDescent_F_ArithGlob
import Definitions.Def_PaddedDescent_F_ArithTop
import Definitions.Def_PaddedDescent_F_ArithWalk
import Definitions.Def_PaddedDescent_F_ArithTopInv
set_option autoImplicit false
section
section
open PaddedDescent PaddedDescent.F PaddedDescent.F.Arith
open PaddedDescent PaddedDescent.F

theorem PaddedDescent.F.Arith.hundred_Ktop_pow_four_le (s : ℕ) : 100 * Ktop s ^ 4 ≤ Ytop s := by sorry
