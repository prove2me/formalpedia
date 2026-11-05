-- Prove2me | Theorems.Thm_PaddedDescent_F_Arith_lin_le_two_pow
-- name    : PaddedDescent.F.Arith.lin_le_two_pow
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T01:45:25.221423+00:00
-- url     : https://prove2.me/theorems/95ae2aa8-d440-48e5-a024-aa449f900f5b
-- title:
--   Arith: lin le two pow
-- statement:
--   s + 8 ≤ 8·2^s.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/PaddedDescent/F/ArithTopInv.lean#L79-L81
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/PaddedDescent/F/ArithTopInv.lean#L79-L81

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

theorem PaddedDescent.F.Arith.lin_le_two_pow (s : ℕ) : s + 8 ≤ 8 * 2 ^ s := by sorry
