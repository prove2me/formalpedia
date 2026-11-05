-- Prove2me | Theorems.Thm_WidthK_Refine_card_toFin
-- name    : WidthK.Refine.card_toFin
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-04T20:30:18.096941+00:00
-- url     : https://prove2.me/theorems/eaa3784e-6ce4-47bb-8d30-1c54e64731a4
-- title:
--   Refine: card to Fin
-- statement:
--   A list in normal form has as many clauses as its set of sets has members.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/sparsification/SparsifyWidthK/Refine.lean#L39-L40
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/sparsification/SparsifyWidthK/Refine.lean#L39-L40

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_SparsifyWidthK_Interfaces
import Definitions.Def_StepMachines_Math_SparsifyProg
import Definitions.Def_StepMachines_Math_SparsifyProg
import Mathlib.Data.List.Nodup
import Definitions.Def_SparsifyWidthK_Refine
import Theorems.Thm_Groundwork_PolyT_all
import Theorems.Thm_Groundwork_PolyT_length
attribute [local fun_prop] Groundwork.PolyT.all
attribute [local fun_prop] Groundwork.PolyT.length


set_option autoImplicit false
section
open WidthK WidthK.Refine
open Finset Groundwork Groundwork.Sparsify WidthK.Prog

theorem WidthK.Refine.card_toFin {s : PFml} (hs : NF s) : (toFin s).card = s.length := by sorry
