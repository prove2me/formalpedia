-- Prove2me | Theorems.Thm_PaddedDescent_F_Arith_one_le_Ytop
-- name    : PaddedDescent.F.Arith.one_le_Ytop
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T03:34:18.657601+00:00
-- url     : https://prove2.me/theorems/c46584ef-2f98-4d5d-9be8-6cf409647157
-- title:
--   Arith: one le Ytop
-- statement:
--   1 ≤ Y.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/PaddedDescent/F/ArithTopInv.lean#L35-L35
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/PaddedDescent/F/ArithTopInv.lean#L35-L35

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

theorem PaddedDescent.F.Arith.one_le_Ytop (s : ℕ) : 1 ≤ Ytop s := by sorry
