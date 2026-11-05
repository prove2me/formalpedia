-- Prove2me | Theorems.Thm_PaddedDescent_F_Mark_Code_enc_append_inj
-- name    : PaddedDescent.F.Mark.Code.enc_append_inj
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T03:30:47.737489+00:00
-- url     : https://prove2.me/theorems/73df9e97-0fdc-4b5d-85cb-1692664a647e
-- title:
--   Code: enc append inj
-- statement:
--   A string of known length is read back from its code, whatever follows the code.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/PaddedDescent/F/MarkCode.lean#L84-L102
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/PaddedDescent/F/MarkCode.lean#L84-L102

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_PaddedDescent_F_Interfaces
import Definitions.Def_StepMachines_Math_Formula
import Definitions.Def_StepMachines_Math_Formula
import Definitions.Def_PaddedDescent_F_MarkCode
import Theorems.Thm_Groundwork_PolyT_all
import Theorems.Thm_Groundwork_PolyT_length
attribute [local fun_prop] Groundwork.PolyT.all
attribute [local fun_prop] Groundwork.PolyT.length


set_option autoImplicit false
section
open PaddedDescent PaddedDescent.F PaddedDescent.F.Mark PaddedDescent.F.Mark.Code
open Groundwork

theorem PaddedDescent.F.Mark.Code.enc_append_inj {β b : ℕ} (h0 : 0 < b) (hb : b ≤ 2 ^ β) {x x' r r' : List Bool} (hl : x.length = x'.length)
    (h : enc β b x ++ r = enc β b x' ++ r') : x = x' ∧ r = r' := by sorry
