-- Prove2me | Theorems.Thm_PaddedDescent_F_RebalF_termM_halts
-- name    : PaddedDescent.F.RebalF.termM_halts
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T02:49:39.068465+00:00
-- url     : https://prove2.me/theorems/dacc6395-76fb-4543-a83a-29f4d2312e2e
-- title:
--   Rebal F: term M halts
-- statement:
--   The Rebal F construction uses the term M halts property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/PaddedDescent/F/RebalF.lean#L97-L101
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/PaddedDescent/F/RebalF.lean#L97-L101

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

theorem PaddedDescent.F.RebalF.termM_halts (K g : ℕ) (F : FNet C) (u : (X0 C × ℕ) × ℕ) : Halts (termM K g F.toP) u (termP K g F u) := by sorry
