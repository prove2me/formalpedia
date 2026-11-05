-- Prove2me | Theorems.Thm_PaddedDescent_F_RebalF_termF_eq
-- name    : PaddedDescent.F.RebalF.termF_eq
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T02:49:48.292839+00:00
-- url     : https://prove2.me/theorems/16024b72-12fa-40ae-9dce-2d81ccd331cb
-- title:
--   Rebal F: term F eq
-- statement:
--   The fuelled `termF` equals the plain `termP`; the bound of the number of labels by the padding
--   length is needed only in the cases where the sum is evaluated.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/PaddedDescent/F/RebalF.lean#L122-L127
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/PaddedDescent/F/RebalF.lean#L122-L127

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_PaddedDescent_F_Table
import Definitions.Def_StepMachines_Prog_NetRun
import Definitions.Def_StepMachines_Prog_NetVal
import Definitions.Def_StepMachines_Prog_GridDefs
import Definitions.Def_Groundwork_Net_Net
import Definitions.Def_PaddedDescent_F_RebalF
import Theorems.Thm_Groundwork_PolyT_length
attribute [local fun_prop] Groundwork.PolyT.length


set_option autoImplicit false
section
section
open PaddedDescent PaddedDescent.F PaddedDescent.F.RebalF
open Groundwork Groundwork.Prog Groundwork.Prog.NetE Groundwork.Stepped Finset
variable {C : Type}

theorem PaddedDescent.F.RebalF.termF_eq {pad : U} {K g : ℕ} {F : FNet C} {u : (X0 C × ℕ) × ℕ}
    (h : isW g u = false → nLab g F.toP u ≤ pad.length) : termF pad K g F u = termP K g F u := by sorry
