-- Prove2me | Theorems.Thm_PaddedDescent_F_Arith_two_pow_le_of_le
-- name    : PaddedDescent.F.Arith.two_pow_le_of_le
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T00:03:30.075037+00:00
-- url     : https://prove2.me/theorems/f0c08ee1-055b-4fb5-b1de-785f92d1e142
-- title:
--   Arith: two pow le of le
-- statement:
--   A power of two with exponent at most 8·X is at most the length F of the pad, if 2^(8·X) ≤ F.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/PaddedDescent/F/ArithTopInv.lean#L342-L343
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/PaddedDescent/F/ArithTopInv.lean#L342-L343

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
variable {k Δ s n F : ℕ}

theorem PaddedDescent.F.Arith.two_pow_le_of_le {e : ℕ} (hF : 2 ^ (8 * Xof s n) ≤ F) (he : e ≤ 8 * Xof s n) : 2 ^ e ≤ F := by sorry
