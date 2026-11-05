-- Prove2me | Theorems.Thm_PaddedDescent_sq_le_four_mul_two_pow
-- name    : PaddedDescent.sq_le_four_mul_two_pow
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-04T20:15:37.308582+00:00
-- url     : https://prove2.me/theorems/400f9855-9fe6-4295-a85a-8d7ada9acf02
-- title:
--   Padded Descent: sq le four mul two pow
-- statement:
--   L² ≤ 4·2^L.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/PaddedDescent/PadRate.lean#L30-L35
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/PaddedDescent/PadRate.lean#L30-L35

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

theorem PaddedDescent.sq_le_four_mul_two_pow (L : ℕ) : L * L ≤ 4 * 2 ^ L := by sorry
