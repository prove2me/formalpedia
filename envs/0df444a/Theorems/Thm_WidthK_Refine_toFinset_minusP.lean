-- Prove2me | Theorems.Thm_WidthK_Refine_toFinset_minusP
-- name    : WidthK.Refine.toFinset_minusP
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-04T20:06:16.81519+00:00
-- url     : https://prove2.me/theorems/1357e060-a4bb-4f62-9aa2-62add1c835a3
-- title:
--   Refine: to Finset minus P
-- statement:
--   `minusP H C` computes the set difference C ∖ H.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/sparsification/SparsifyWidthK/Refine.lean#L68-L70
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/sparsification/SparsifyWidthK/Refine.lean#L68-L70

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_SparsifyWidthK_Interfaces
import Definitions.Def_StepMachines_Math_SparsifyProg
import Definitions.Def_StepMachines_Math_SparsifyProg
import Mathlib.Data.List.Nodup
import Definitions.Def_SparsifyWidthK_Refine
import Theorems.Thm_Groundwork_PolyT_all
attribute [local fun_prop] Groundwork.PolyT.all


set_option autoImplicit false
section
open WidthK WidthK.Refine
open Finset Groundwork Groundwork.Sparsify WidthK.Prog

theorem WidthK.Refine.toFinset_minusP (H C : PCl) : (minusP H C).toFinset = C.toFinset \ H.toFinset := by sorry
