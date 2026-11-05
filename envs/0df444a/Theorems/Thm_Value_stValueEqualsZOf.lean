-- Prove2me | Theorems.Thm_Value_stValueEqualsZOf
-- name    : Value.stValueEqualsZOf
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T02:24:09.937676+00:00
-- url     : https://prove2.me/theorems/5a5d4589-acbe-4dc2-9c9d-ba04790e6002
-- title:
--   Value: st Value Equals ZOf
-- statement:
--   «so the value equals Z», from the sentences before it.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/networks/Value/End.lean#L31-L35
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/networks/Value/End.lean#L31-L35

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_Value_Clique
import Definitions.Def_Value_Joint
import Definitions.Def_Value_End
set_option autoImplicit false
section
section
open Value
open Groundwork Groundwork.Prog Groundwork.Prog.NetE Finset Eight.SecNetworks Eight.ViaGrouping

theorem Value.stValueEqualsZOf : StValueEqualsZOf := by sorry
