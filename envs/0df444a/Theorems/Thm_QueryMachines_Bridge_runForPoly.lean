-- Prove2me | Theorems.Thm_QueryMachines_Bridge_runForPoly
-- name    : QueryMachines.Bridge.runForPoly
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T02:15:31.539458+00:00
-- url     : https://prove2.me/theorems/f94dc0f9-c021-4996-9f23-ea81a13ddfd6
-- title:
--   Bridge: run For Poly
-- statement:
--   `runFor N` is polynomial-time for every step machine N with polynomial-time steps.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/CountedToPadded/RunFor.lean#L119-L119
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/CountedToPadded/RunFor.lean#L119-L119

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_CountedToPadded_Defs
import Definitions.Def_CountedToPadded_Compare
import Definitions.Def_ToTuring_Closure_Fold
import Definitions.Def_ToTuring_Lib_List1b
import Definitions.Def_CountedToPadded_RunFor
set_option autoImplicit false
section
section
open QueryMachines QueryMachines.Bridge
open Groundwork Groundwork.PolyT PaddedDescent.F Proof

theorem QueryMachines.Bridge.runForPoly : RunForPoly := by sorry
