-- Prove2me | Theorems.Thm_PaddedDescent_F_RebalF_mergedM_halts
-- name    : PaddedDescent.F.RebalF.mergedM_halts
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T02:49:49.732542+00:00
-- url     : https://prove2.me/theorems/790d8b17-7c9c-46e9-808e-2c04e22f00ca
-- title:
--   Rebal F: merged M halts
-- statement:
--   The Rebal F construction uses the merged M halts property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/PaddedDescent/F/RebalF.lean#L103-L105
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/PaddedDescent/F/RebalF.lean#L103-L105

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_PaddedDescent_F_Table
import Definitions.Def_StepMachines_Prog_NetRun
import Definitions.Def_StepMachines_Prog_NetVal
import Definitions.Def_StepMachines_Prog_GridDefs
import Definitions.Def_Groundwork_Net_Net
import Definitions.Def_PaddedDescent_F_RebalF
set_option autoImplicit false
section
section
open PaddedDescent PaddedDescent.F PaddedDescent.F.RebalF
open Groundwork Groundwork.Prog Groundwork.Prog.NetE Groundwork.Stepped Finset
variable {C : Type}
variable [HasSize C]

theorem PaddedDescent.F.RebalF.mergedM_halts (K g : ℕ) (F : FNet C) (u : X0 C) : Halts (mergedM K g F.toP) u (mergedP K g F u) := by sorry
