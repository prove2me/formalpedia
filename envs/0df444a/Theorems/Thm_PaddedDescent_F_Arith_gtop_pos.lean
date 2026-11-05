-- Prove2me | Theorems.Thm_PaddedDescent_F_Arith_gtop_pos
-- name    : PaddedDescent.F.Arith.gtop_pos
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T01:45:06.334382+00:00
-- url     : https://prove2.me/theorems/2fb4c242-acef-4f2b-b8a0-7522f95de9f8
-- title:
--   Arith: gtop pos
-- statement:
--   `gtop` is positive.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/PaddedDescent/F/ArithTopInv.lean#L43-L43
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/PaddedDescent/F/ArithTopInv.lean#L43-L43

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

theorem PaddedDescent.F.Arith.gtop_pos (s : ℕ) : 0 < gtop s := by sorry
