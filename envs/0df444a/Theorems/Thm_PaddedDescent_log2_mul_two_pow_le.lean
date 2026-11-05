-- Prove2me | Theorems.Thm_PaddedDescent_log2_mul_two_pow_le
-- name    : PaddedDescent.log2_mul_two_pow_le
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-04T20:15:24.494203+00:00
-- url     : https://prove2.me/theorems/f2b8fc4e-c011-4481-a9f2-7b100707929c
-- title:
--   Padded Descent: log2 mul two pow le
-- statement:
--   If 2^s ≤ ⌊log₂(n+2)⌋ then ⌊log₂(n+2)⌋·2^s ≤ 8·(n + 2^s).
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/PaddedDescent/PadRate.lean#L38-L43
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/PaddedDescent/PadRate.lean#L38-L43

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_ThreeSatRateStatement
import Definitions.Def_PaddedDescent_Params
import Definitions.Def_PaddedDescent_Pad
import Definitions.Def_PaddedDescent_RateLemmas
import Definitions.Def_PaddedDescent_PadRate
set_option autoImplicit false
section
open PaddedDescent
open Groundwork Sat3 Turing

theorem PaddedDescent.log2_mul_two_pow_le {n s : ℕ} (hs : 2 ^ s ≤ Nat.log2 (n + 2)) : Nat.log2 (n + 2) * 2 ^ s ≤ 8 * (n + 2 ^ s) := by sorry
