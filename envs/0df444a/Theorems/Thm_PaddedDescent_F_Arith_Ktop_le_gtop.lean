-- Prove2me | Theorems.Thm_PaddedDescent_F_Arith_Ktop_le_gtop
-- name    : PaddedDescent.F.Arith.Ktop_le_gtop
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T00:48:08.480845+00:00
-- url     : https://prove2.me/theorems/d2bdcf5a-cbdd-4f26-ae67-ab4bf008cde1
-- title:
--   Arith: Ktop le gtop
-- statement:
--   K_t ≤ `gtop` = 3·K_t⁸.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/PaddedDescent/F/ArithTopInv.lean#L38-L40
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/PaddedDescent/F/ArithTopInv.lean#L38-L40

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

theorem PaddedDescent.F.Arith.Ktop_le_gtop (s : ℕ) : Ktop s ≤ gtop s := by sorry
