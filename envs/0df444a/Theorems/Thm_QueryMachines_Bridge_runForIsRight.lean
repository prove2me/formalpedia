-- Prove2me | Theorems.Thm_QueryMachines_Bridge_runForIsRight
-- name    : QueryMachines.Bridge.runForIsRight
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-05T02:15:40.01806+00:00
-- url     : https://prove2.me/theorems/b97c0085-5c82-456f-b2b8-b99e7494e1bb
-- title:
--   Bridge: run For Is Right
-- statement:
--   `runFor` returns the result of the machine once fuel and room suffice.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/CountedToPadded/RunFor.lean#L83-L87
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/CountedToPadded/RunFor.lean#L83-L87

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

theorem QueryMachines.Bridge.runForIsRight : RunForIsRight := by sorry
