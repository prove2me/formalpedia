-- Prove2me | Theorems.Thm_P2M_WidthK_Refine_subP_iff__c9db5ddc349e
-- name    : P2M_WidthK_Refine_subP_iff__c9db5ddc349e
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-04T20:05:54.194949+00:00
-- url     : https://prove2.me/theorems/de0259ff-8c27-4ef7-b39a-52e8278ecaf6
-- title:
--   P2 M Width K Refine sub P iff  c9db5ddc349e: P2 M Width K Refine sub P iff  c9db5ddc349e
-- statement:
--   `subP D C` tests inclusion of the sets of literals.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/sparsification/SparsifyWidthK/Refine.lean#L47-L48
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/sparsification/SparsifyWidthK/Refine.lean#L47-L48

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

theorem P2M_WidthK_Refine_subP_iff__c9db5ddc349e (D C : PCl) : subP D C = true ↔ D.toFinset ⊆ C.toFinset := by sorry

alias «WidthK».«Refine».«subP_iff'» := P2M_WidthK_Refine_subP_iff__c9db5ddc349e
