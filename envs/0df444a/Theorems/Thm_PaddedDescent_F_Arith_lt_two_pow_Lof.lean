-- Prove2me | Theorems.Thm_PaddedDescent_F_Arith_lt_two_pow_Lof
-- name    : PaddedDescent.F.Arith.lt_two_pow_Lof
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T03:34:00.199226+00:00
-- url     : https://prove2.me/theorems/b2d927c4-9c65-40b8-8d36-059ba42676a6
-- title:
--   Arith: lt two pow Lof
-- statement:
--   n < 2^L.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/PaddedDescent/F/ArithTopInv.lean#L196-L197
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/PaddedDescent/F/ArithTopInv.lean#L196-L197

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

theorem PaddedDescent.F.Arith.lt_two_pow_Lof (s n : ℕ) : n < 2 ^ Lof s n := by sorry
