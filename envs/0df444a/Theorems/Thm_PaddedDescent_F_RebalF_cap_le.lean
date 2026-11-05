-- Prove2me | Theorems.Thm_PaddedDescent_F_RebalF_cap_le
-- name    : PaddedDescent.F.RebalF.cap_le
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-04T23:56:10.727174+00:00
-- url     : https://prove2.me/theorems/24db32d5-57fe-4941-b68c-11a04ef98a48
-- title:
--   Rebal F: cap le
-- statement:
--   The Rebal F construction uses the cap le property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/PaddedDescent/F/RebalF.lean#L146-L150
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/PaddedDescent/F/RebalF.lean#L146-L150

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_PaddedDescent_F_Table
import Definitions.Def_StepMachines_Prog_NetRun
import Definitions.Def_StepMachines_Prog_NetVal
import Definitions.Def_StepMachines_Prog_GridDefs
import Definitions.Def_Groundwork_Net_Net
import Definitions.Def_PaddedDescent_F_RebalF
import Theorems.Thm_Groundwork_Prog_NetE_cap_le

set_option autoImplicit false
section
section
open PaddedDescent PaddedDescent.F PaddedDescent.F.RebalF
open Groundwork Groundwork.Prog Groundwork.Prog.NetE Groundwork.Stepped Finset
variable {C : Type}

theorem PaddedDescent.F.RebalF.cap_le {F : FNet C} {c : C} {g : ℕ} {N : Network (Fin g) (List Bool) (List Bool)} {P B : ℕ}
    (hN : F.toP.Presents c N 0 0) (hS : N.Sized P B) {a b : Fin g} (hab : a ≠ b) : F.toP.cap c a b ≤ P := by sorry
