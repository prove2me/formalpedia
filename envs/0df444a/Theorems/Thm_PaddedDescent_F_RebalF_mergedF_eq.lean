-- Prove2me | Theorems.Thm_PaddedDescent_F_RebalF_mergedF_eq
-- name    : PaddedDescent.F.RebalF.mergedF_eq
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T00:25:45.813869+00:00
-- url     : https://prove2.me/theorems/828142e0-9047-4e6a-b0c6-8bf926f4e52b
-- title:
--   Rebal F: merged F eq
-- statement:
--   The Rebal F construction uses the merged F eq property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/PaddedDescent/F/RebalF.lean#L129-L136
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/PaddedDescent/F/RebalF.lean#L129-L136

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

theorem PaddedDescent.F.RebalF.mergedF_eq {pad : U} {K g : ℕ} {F : FNet C} {u : X0 C} (h1 : nStates K g F.toP u ≤ pad.length)
    (h2 : ∀ y, ∀ i < g * g, isW g ((u, y), i) = false → nLab g F.toP ((u, y), i) ≤ pad.length) :
    mergedF pad K g F u = mergedP K g F u := by sorry
