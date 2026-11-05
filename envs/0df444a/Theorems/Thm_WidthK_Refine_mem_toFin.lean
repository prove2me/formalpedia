-- Prove2me | Theorems.Thm_WidthK_Refine_mem_toFin
-- name    : WidthK.Refine.mem_toFin
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-04T19:35:34.579783+00:00
-- url     : https://prove2.me/theorems/0f82754c-c1e2-4735-bf81-569a1a7b8e73
-- title:
--   Refine: mem to Fin
-- statement:
--   The members of `toFin s` are the clauses of s, read as sets.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/sparsification/SparsifyWidthK/Refine.lean#L35-L36
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/sparsification/SparsifyWidthK/Refine.lean#L35-L36

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

theorem WidthK.Refine.mem_toFin {s : PFml} {X : Finset PLit} : X ∈ toFin s ↔ ∃ C ∈ s, C.toFinset = X := by sorry
