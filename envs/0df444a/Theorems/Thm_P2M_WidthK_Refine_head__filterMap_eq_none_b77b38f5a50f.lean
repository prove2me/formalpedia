-- Prove2me | Theorems.Thm_P2M_WidthK_Refine_head__filterMap_eq_none_b77b38f5a50f
-- name    : P2M_WidthK_Refine_head__filterMap_eq_none_b77b38f5a50f
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-04T20:30:35.660377+00:00
-- url     : https://prove2.me/theorems/1e4ddd2d-e9c9-4284-b0cc-8a0d65cc4807
-- title:
--   P2 M Width K Refine head  filter Map eq none b77b38f5a50f: P2 M Width K Refine head  filter Map eq none b77b38f5a50f
-- statement:
--   If `(l.filterMap f).head?` is `none`, then f has no result at any entry of l.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/sparsification/SparsifyWidthK/Refine.lean#L212-L215
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/sparsification/SparsifyWidthK/Refine.lean#L212-L215

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_SparsifyWidthK_Interfaces
import Definitions.Def_StepMachines_Math_SparsifyProg
import Definitions.Def_StepMachines_Math_SparsifyProg
import Mathlib.Data.List.Nodup
import Definitions.Def_SparsifyWidthK_Refine
import Theorems.Thm_Groundwork_PolyT_all
import Theorems.Thm_Groundwork_PolyT_filterMap
attribute [local fun_prop] Groundwork.PolyT.all
attribute [local fun_prop] Groundwork.PolyT.filterMap


set_option autoImplicit false
section
open WidthK WidthK.Refine
open Finset Groundwork Groundwork.Sparsify WidthK.Prog

theorem P2M_WidthK_Refine_head__filterMap_eq_none_b77b38f5a50f {α β : Type*} {f : α → Option β} {l : List α}
    (h : (l.filterMap f).head? = none) : ∀ x ∈ l, f x = none := by sorry

alias «WidthK».«Refine».«head?_filterMap_eq_none» := P2M_WidthK_Refine_head__filterMap_eq_none_b77b38f5a50f
