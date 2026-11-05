-- Prove2me | Theorems.Thm_PaddedDescent_F_Mark_Code_le_blocks_mul
-- name    : PaddedDescent.F.Mark.Code.le_blocks_mul
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T01:42:34.49182+00:00
-- url     : https://prove2.me/theorems/97d64ccb-fef4-40d5-ba0a-3ac4c2307c34
-- title:
--   Code: le blocks mul
-- statement:
--   The blocks of b bits cover a string of t bits.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/PaddedDescent/F/MarkCode.lean#L42-L46
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/PaddedDescent/F/MarkCode.lean#L42-L46

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

theorem PaddedDescent.F.Mark.Code.le_blocks_mul {b : ℕ} (h0 : 0 < b) (t : ℕ) : t ≤ (t + b - 1) / b * b := by sorry
