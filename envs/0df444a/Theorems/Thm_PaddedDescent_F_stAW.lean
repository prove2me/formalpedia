-- Prove2me | Theorems.Thm_PaddedDescent_F_stAW
-- name    : PaddedDescent.F.stAW
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T03:34:30.262564+00:00
-- url     : https://prove2.me/theorems/985cc61c-87e5-4703-9859-3002525c251d
-- title:
--   F: st AW
-- statement:
--   The arithmetic that knows the width.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/PaddedDescent/F/ArithA.lean#L61-L62
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/PaddedDescent/F/ArithA.lean#L61-L62

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_PaddedDescent_F_Interfaces
import Definitions.Def_PaddedDescent_F_ArithSched
import Definitions.Def_PaddedDescent_F_ArithFits
import Definitions.Def_PaddedDescent_F_ArithTopInv
import Definitions.Def_PaddedDescent_F_ArithMark
import Definitions.Def_PaddedDescent_F_ArithA
set_option autoImplicit false
section
section
open PaddedDescent PaddedDescent.F
open Arith

theorem PaddedDescent.F.stAW : StAW := by sorry
