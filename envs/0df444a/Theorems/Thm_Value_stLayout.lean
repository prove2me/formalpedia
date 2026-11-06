-- Prove2me | Theorems.Thm_Value_stLayout
-- name    : Value.stLayout
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T04:01:45.177006+00:00
-- url     : https://prove2.me/theorems/ac77adc0-4bed-4c8d-8f30-7176f86ad513
-- title:
--   Value: st Layout
-- statement:
--   «For each pair of groups {γ, γ'} choose an order of the pairs {a, b} … In this order, the pair
--   {a, b} is assigned a block of c_{a,b} consecutive positions of {1, …, L}; the L − Y_{γ,γ'} positions
--   after the last block hold the appended bits.»
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/networks/Value/Blocks.lean#L37-L53
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/networks/Value/Blocks.lean#L37-L53

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_Value_Words
import Definitions.Def_StepMachines_Prog_NetVal
import Definitions.Def_StepMachines_Prog_NetVal
import Definitions.Def_Value_Blocks
import Theorems.Thm_Groundwork_PolyT_all
attribute [local fun_prop] Groundwork.PolyT.all


set_option autoImplicit false
section
section
open Value
open Groundwork Groundwork.Prog Groundwork.Prog.NetE Finset Eight.SecNetworks Eight.ViaGrouping

theorem Value.stLayout : StLayout := by sorry
