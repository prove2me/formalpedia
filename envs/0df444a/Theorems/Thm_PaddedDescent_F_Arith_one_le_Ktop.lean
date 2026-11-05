-- Prove2me | Theorems.Thm_PaddedDescent_F_Arith_one_le_Ktop
-- name    : PaddedDescent.F.Arith.one_le_Ktop
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-04T23:44:26.290019+00:00
-- url     : https://prove2.me/theorems/8f2c60e3-c648-4f66-8d30-55b0b688f700
-- title:
--   Arith: one le Ktop
-- statement:
--   1 ≤ K_t.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/PaddedDescent/F/ArithTopInv.lean#L32-L32
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/PaddedDescent/F/ArithTopInv.lean#L32-L32

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

theorem PaddedDescent.F.Arith.one_le_Ktop (s : ℕ) : 1 ≤ Ktop s := by sorry
