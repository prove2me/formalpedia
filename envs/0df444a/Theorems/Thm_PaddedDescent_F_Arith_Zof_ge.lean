-- Prove2me | Theorems.Thm_PaddedDescent_F_Arith_Zof_ge
-- name    : PaddedDescent.F.Arith.Zof_ge
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T03:34:22.574586+00:00
-- url     : https://prove2.me/theorems/39306e57-21e6-4629-aad7-c6a56b0fc6e1
-- title:
--   Arith: Zof ge
-- statement:
--   25·K_t² ≤ 2·Z.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/PaddedDescent/F/ArithTopInv.lean#L155-L159
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/PaddedDescent/F/ArithTopInv.lean#L155-L159

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

theorem PaddedDescent.F.Arith.Zof_ge (s : ℕ) : 25 * Kseq (depthOf s) ^ 2 ≤ 2 * Zof s := by sorry
