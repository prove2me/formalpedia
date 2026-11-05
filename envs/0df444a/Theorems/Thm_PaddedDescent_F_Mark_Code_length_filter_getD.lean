-- Prove2me | Theorems.Thm_PaddedDescent_F_Mark_Code_length_filter_getD
-- name    : PaddedDescent.F.Mark.Code.length_filter_getD
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T03:30:39.531099+00:00
-- url     : https://prove2.me/theorems/cf4a5fa7-ce8a-4a10-a1df-c48dd4b336fd
-- title:
--   Code: length filter get D
-- statement:
--   The places below M, where M is at least the length of x, that hold a one are as many as the ones
--   of x.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/PaddedDescent/F/MarkCode.lean#L116-L126
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/PaddedDescent/F/MarkCode.lean#L116-L126

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_PaddedDescent_F_Interfaces
import Definitions.Def_StepMachines_Math_Formula
import Definitions.Def_StepMachines_Math_Formula
import Definitions.Def_PaddedDescent_F_MarkCode
import Theorems.Thm_Groundwork_PolyT_all
import Theorems.Thm_Groundwork_PolyT_count
import Theorems.Thm_Groundwork_PolyT_filter
import Theorems.Thm_Groundwork_PolyT_length
attribute [local fun_prop] Groundwork.PolyT.all
attribute [local fun_prop] Groundwork.PolyT.count
attribute [local fun_prop] Groundwork.PolyT.filter
attribute [local fun_prop] Groundwork.PolyT.length


set_option autoImplicit false
section
open PaddedDescent PaddedDescent.F PaddedDescent.F.Mark PaddedDescent.F.Mark.Code
open Groundwork

theorem PaddedDescent.F.Mark.Code.length_filter_getD : ∀ (x : List Bool) (M : ℕ), x.length ≤ M → ((List.range M).filter fun i => x.getD i false).length = x.count true
  := by sorry
