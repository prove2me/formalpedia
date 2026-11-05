-- Prove2me | Theorems.Thm_PaddedDescent_F_Arith_coeff_le_Ktop
-- name    : PaddedDescent.F.Arith.coeff_le_Ktop
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T03:34:17.484197+00:00
-- url     : https://prove2.me/theorems/af2825e0-a576-4a2d-896b-81135e4a053d
-- title:
--   Arith: coeff le Ktop
-- statement:
--   4·(s + 8)⁶·2^s ≤ K_t.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/PaddedDescent/F/ArithTopInv.lean#L132-L136
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/PaddedDescent/F/ArithTopInv.lean#L132-L136

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

theorem PaddedDescent.F.Arith.coeff_le_Ktop (s : ℕ) : 4 * (s + 8) ^ 6 * 2 ^ s ≤ Ktop s := by sorry
