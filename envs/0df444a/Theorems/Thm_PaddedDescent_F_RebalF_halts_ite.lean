-- Prove2me | Theorems.Thm_PaddedDescent_F_RebalF_halts_ite
-- name    : PaddedDescent.F.RebalF.halts_ite
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T01:13:44.018132+00:00
-- url     : https://prove2.me/theorems/c13cdbe0-dd15-4798-b386-5c6eaa739a72
-- title:
--   Rebal F: halts ite
-- statement:
--   The Rebal F construction uses the halts ite property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/PaddedDescent/F/RebalF.lean#L68-L74
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/PaddedDescent/F/RebalF.lean#L68-L74

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
variable {α β : Type}

theorem PaddedDescent.F.RebalF.halts_ite {p : α → Bool} {M N : Stepped α β} {a : α} {b c : β} (h1 : Halts M a b) (h2 : Halts N a c) :
    Halts (Stepped.ite p M N) a (bif p a then b else c) := by sorry
