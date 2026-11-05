-- Prove2me | Theorems.Thm_PaddedDescent_F_Arith_coeff_le
-- name    : PaddedDescent.F.Arith.coeff_le
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T01:45:16.650679+00:00
-- url     : https://prove2.me/theorems/81f354bd-d772-4b99-9d0c-2082de3ec524
-- title:
--   Arith: coeff le
-- statement:
--   4·(s + 8)⁶ ≤ 2^(6s+20).
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/PaddedDescent/F/ArithTopInv.lean#L84-L86
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/PaddedDescent/F/ArithTopInv.lean#L84-L86

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

theorem PaddedDescent.F.Arith.coeff_le (s : ℕ) : 4 * (s + 8) ^ 6 ≤ 2 ^ (6 * s + 20) := by sorry
