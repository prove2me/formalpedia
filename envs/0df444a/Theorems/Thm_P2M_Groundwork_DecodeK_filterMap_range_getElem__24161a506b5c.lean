-- Prove2me | Theorems.Thm_P2M_Groundwork_DecodeK_filterMap_range_getElem__24161a506b5c
-- name    : P2M_Groundwork_DecodeK_filterMap_range_getElem__24161a506b5c
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-04T16:23:40.091384+00:00
-- url     : https://prove2.me/theorems/bff764e9-502c-4e25-a579-0b70d5a07f81
-- title:
--   P2 M Groundwork Decode K filter Map range get Elem  24161a506b5c: P2 M Groundwork Decode K filter Map range get Elem  24161a506b5c
-- statement:
--   Reading the first k places of a list one by one gives its first k members.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/consequences/WidthK/Decode.lean#L66-L71
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/consequences/WidthK/Decode.lean#L66-L71

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_KSatStatement
import Definitions.Def_StepMachines_Prog_Decode
import Definitions.Def_StepMachines_Prog_Decode
import Definitions.Def_StepMachines_Prog_Decode
import Definitions.Def_StepMachines_Math_Formula
import Definitions.Def_StepMachines_Math_Formula
import Definitions.Def_WidthK_Decode
set_option autoImplicit false
section
open Groundwork Groundwork.DecodeK
open Sat3 (Lit CNF Satisfiable slot)
open SatK
open Groundwork.Decode

theorem P2M_Groundwork_DecodeK_filterMap_range_getElem__24161a506b5c {α : Type} (l : List α) (k : ℕ) : (List.range k).filterMap (fun j => l[j]?) = l.take k := by sorry

alias «Groundwork».«DecodeK».«filterMap_range_getElem?» := P2M_Groundwork_DecodeK_filterMap_range_getElem__24161a506b5c
