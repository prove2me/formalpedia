-- Prove2me | Theorems.Thm_WidthK_Refine_toFin_petals
-- name    : WidthK.Refine.toFin_petals
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-04T20:29:59.971622+00:00
-- url     : https://prove2.me/theorems/5a78a4f5-7595-44f4-b318-3c4c25f03426
-- title:
--   Refine: to Fin petals
-- statement:
--   The second component of the answer of `tryP` stands for the petals.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/sparsification/SparsifyWidthK/Refine.lean#L73-L82
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/sparsification/SparsifyWidthK/Refine.lean#L73-L82

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_SparsifyWidthK_Interfaces
import Definitions.Def_StepMachines_Math_SparsifyProg
import Definitions.Def_StepMachines_Math_SparsifyProg
import Mathlib.Data.List.Nodup
import Definitions.Def_SparsifyWidthK_Refine
import Theorems.Thm_Groundwork_PolyT_all
import Theorems.Thm_Groundwork_PolyT_map
attribute [local fun_prop] Groundwork.PolyT.all
attribute [local fun_prop] Groundwork.PolyT.map


set_option autoImplicit false
section
open WidthK WidthK.Refine
open Finset Groundwork Groundwork.Sparsify WidthK.Prog

theorem WidthK.Refine.toFin_petals {s : PFml} (hs : ∀ C ∈ s, C.Nodup) (j : ℕ) (H : PCl) :
    toFin ((overP s j H).map (minusP H)) = (Sparsify.over (toFin s) j H.toFinset).image fun C => C \ H.toFinset := by sorry
