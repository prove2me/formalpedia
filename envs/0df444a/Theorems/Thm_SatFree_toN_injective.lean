-- Prove2me | Theorems.Thm_SatFree_toN_injective
-- name    : SatFree.toN_injective
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T09:32:38.131808+00:00
-- url     : https://prove2.me/theorems/6374d710-7ba0-40ee-b62e-4373164b99f7
-- title:
--   Sat Free: to N injective
-- statement:
--   A formula is determined by the same formula with numbers as variables.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/consequences/FreeCode/Main.lean#L42-L45
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/consequences/FreeCode/Main.lean#L42-L45

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_KSatFreeCodeStatement
import Definitions.Def_FreeCode_Defs
import Definitions.Def_FreeCode_Reader
import Definitions.Def_FreeCode_Order
import Definitions.Def_FreeCode_Random
import Definitions.Def_FreeCode_Behind
import Definitions.Def_FreeCode_Brute
import Definitions.Def_FreeCode_Tied
import Definitions.Def_ToTuring_Machine_EndTM
import Mathlib.Tactic
import Definitions.Def_FreeCode_Main
set_option autoImplicit false
section
section
open SatFree
open Groundwork FreeCode
open scoped NNReal ENNReal

theorem SatFree.toN_injective {n : ℕ} : Function.Injective (Decode.toN (n := n)) := by sorry
