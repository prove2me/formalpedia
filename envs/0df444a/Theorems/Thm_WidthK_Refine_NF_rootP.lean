-- Prove2me | Theorems.Thm_WidthK_Refine_NF_rootP
-- name    : WidthK.Refine.NF_rootP
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-04T20:31:02.868683+00:00
-- url     : https://prove2.me/theorems/c20af772-5d51-4490-a218-a1f7fc4f5324
-- title:
--   Refine: NF root P
-- statement:
--   `rootP ψ` is in normal form (from `nodeP_root` of `StepMachines/Math/SparsifyProg.lean`).
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/sparsification/SparsifyWidthK/Refine.lean#L315-L317
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/sparsification/SparsifyWidthK/Refine.lean#L315-L317

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

theorem WidthK.Refine.NF_rootP (ψ : PFml) : NF (rootP ψ) := by sorry
