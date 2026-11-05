-- Prove2me | Theorems.Thm_WidthK_Refine_toFin_overP
-- name    : WidthK.Refine.toFin_overP
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-04T20:06:38.671194+00:00
-- url     : https://prove2.me/theorems/b54138c9-68de-4654-bb71-a72e061a548c
-- title:
--   Refine: to Fin over P
-- statement:
--   `overP s j H` lists the clauses of size j that contain H: it computes `over`.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/sparsification/SparsifyWidthK/Refine.lean#L51-L59
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/sparsification/SparsifyWidthK/Refine.lean#L51-L59

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

theorem WidthK.Refine.toFin_overP {s : PFml} (hs : ∀ C ∈ s, C.Nodup) (j : ℕ) (H : PCl) :
    toFin (overP s j H) = Sparsify.over (toFin s) j H.toFinset := by sorry
