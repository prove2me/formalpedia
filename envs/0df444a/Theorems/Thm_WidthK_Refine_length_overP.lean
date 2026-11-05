-- Prove2me | Theorems.Thm_WidthK_Refine_length_overP
-- name    : WidthK.Refine.length_overP
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-04T20:06:40.808375+00:00
-- url     : https://prove2.me/theorems/d1bcbe0c-cc9f-4993-9b74-983378041577
-- title:
--   Refine: length over P
-- statement:
--   The number that the search compares with the threshold is the number of clauses of size j over
--   H.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/sparsification/SparsifyWidthK/Refine.lean#L63-L65
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/sparsification/SparsifyWidthK/Refine.lean#L63-L65

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

theorem WidthK.Refine.length_overP {s : PFml} (hs : NF s) (j : ℕ) (H : PCl) :
    (overP s j H).length = (Sparsify.over (toFin s) j H.toFinset).card := by sorry
