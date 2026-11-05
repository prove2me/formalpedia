-- Prove2me | Theorems.Thm_WidthK_Refine_toFin_rootP
-- name    : WidthK.Refine.toFin_rootP
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-04T19:42:01.09922+00:00
-- url     : https://prove2.me/theorems/75dcb3a0-2a94-45fd-85cf-89f5c4969e94
-- title:
--   Refine: to Fin root P
-- statement:
--   `rootP ψ` stands for the inclusion-minimal clauses of ψ (`toFinset_rootP` of
--   `StepMachines/Math/SparsifyProg.lean`).
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/sparsification/SparsifyWidthK/Refine.lean#L312-L312
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/sparsification/SparsifyWidthK/Refine.lean#L312-L312

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

theorem WidthK.Refine.toFin_rootP (ψ : PFml) : toFin (rootP ψ) = red (toFin ψ) := by sorry
