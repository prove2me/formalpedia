-- Prove2me | Theorems.Thm_PaddedDescent_F_Arith_cube_le_Ytop
-- name    : PaddedDescent.F.Arith.cube_le_Ytop
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T01:45:04.655534+00:00
-- url     : https://prove2.me/theorems/7d5eeb14-8269-4219-b691-fc94e8bbfd10
-- title:
--   Arith: cube le Ytop
-- statement:
--   8·(s + 8)³ + 1 ≤ Y.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/PaddedDescent/F/ArithTopInv.lean#L89-L96
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/PaddedDescent/F/ArithTopInv.lean#L89-L96

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

theorem PaddedDescent.F.Arith.cube_le_Ytop (s : ℕ) : 8 * (s + 8) ^ 3 + 1 ≤ Ytop s := by sorry
