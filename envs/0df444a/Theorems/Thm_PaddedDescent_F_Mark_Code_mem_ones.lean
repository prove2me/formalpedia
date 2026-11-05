-- Prove2me | Theorems.Thm_PaddedDescent_F_Mark_Code_mem_ones
-- name    : PaddedDescent.F.Mark.Code.mem_ones
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T01:41:48.55985+00:00
-- url     : https://prove2.me/theorems/b9f15deb-0be3-4532-80da-4e6096d1901f
-- title:
--   Code: mem ones
-- statement:
--   p is listed for block o exactly when p < b and x has a one at the place o·b + p.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/PaddedDescent/F/MarkCode.lean#L38-L39
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/PaddedDescent/F/MarkCode.lean#L38-L39

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_PaddedDescent_F_Interfaces
import Definitions.Def_StepMachines_Math_Formula
import Definitions.Def_StepMachines_Math_Formula
import Definitions.Def_PaddedDescent_F_MarkCode
import Theorems.Thm_Groundwork_PolyT_all
attribute [local fun_prop] Groundwork.PolyT.all


set_option autoImplicit false
section
open PaddedDescent PaddedDescent.F PaddedDescent.F.Mark PaddedDescent.F.Mark.Code
open Groundwork

theorem PaddedDescent.F.Mark.Code.mem_ones {b : ℕ} {x : List Bool} {o p : ℕ} : p ∈ ones b x o ↔ p < b ∧ x.getD (o * b + p) false = true := by sorry
