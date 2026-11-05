-- Prove2me | Theorems.Thm_PaddedDescent_F_Arith_small
-- name    : PaddedDescent.F.Arith.small
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T00:49:15.970751+00:00
-- url     : https://prove2.me/theorems/bc189b7e-a7ad-4aed-9c9f-17962889a6c7
-- title:
--   Arith: small
-- statement:
--   The sum of all overheads: 5·Z + L·(2·K_t² + 2) + 1 + K_t ≤ ⌊n/2^s⌋.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/PaddedDescent/F/ArithTopInv.lean#L234-L250
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/PaddedDescent/F/ArithTopInv.lean#L234-L250

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

theorem PaddedDescent.F.Arith.small {s n : ℕ} (hY : Ytop s ^ 6 ≤ n) :
    5 * Zof s + Lof s n * (2 * Ktop s ^ 2 + 2) + 1 + Ktop s ≤ n / 2 ^ s := by sorry
