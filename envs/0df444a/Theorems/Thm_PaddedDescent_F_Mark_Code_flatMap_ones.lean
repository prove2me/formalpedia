-- Prove2me | Theorems.Thm_PaddedDescent_F_Mark_Code_flatMap_ones
-- name    : PaddedDescent.F.Mark.Code.flatMap_ones
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T03:29:58.711145+00:00
-- url     : https://prove2.me/theorems/814e1c09-0216-4d1d-8d59-3d04ee8aaaf7
-- title:
--   Code: flat Map ones
-- statement:
--   The ones of the first N blocks, with their places in x, are the places below N·b that hold a
--   one.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/PaddedDescent/F/MarkCode.lean#L130-L136
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/PaddedDescent/F/MarkCode.lean#L130-L136

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_PaddedDescent_F_Interfaces
import Definitions.Def_StepMachines_Math_Formula
import Definitions.Def_StepMachines_Math_Formula
import Definitions.Def_PaddedDescent_F_MarkCode
import Theorems.Thm_Groundwork_PolyT_all
import Theorems.Thm_Groundwork_PolyT_filter
import Theorems.Thm_Groundwork_PolyT_flatMap
import Theorems.Thm_Groundwork_PolyT_map
attribute [local fun_prop] Groundwork.PolyT.all
attribute [local fun_prop] Groundwork.PolyT.filter
attribute [local fun_prop] Groundwork.PolyT.flatMap
attribute [local fun_prop] Groundwork.PolyT.map


set_option autoImplicit false
section
open PaddedDescent PaddedDescent.F PaddedDescent.F.Mark PaddedDescent.F.Mark.Code
open Groundwork

theorem PaddedDescent.F.Mark.Code.flatMap_ones (b : ℕ) (x : List Bool) (N : ℕ) :
    (List.range N).flatMap (fun o => (ones b x o).map (o * b + ·)) = (List.range (N * b)).filter fun i => x.getD i false := by sorry
