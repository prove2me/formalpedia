-- Prove2me | Theorems.Thm_PaddedDescent_F_RebalF_halts_free
-- name    : PaddedDescent.F.RebalF.halts_free
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T02:49:42.403816+00:00
-- url     : https://prove2.me/theorems/5f5e57b3-633a-4499-acd9-018ee375538f
-- title:
--   Rebal F: halts free
-- statement:
--   The Rebal F construction uses the halts free property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/PaddedDescent/F/RebalF.lean#L76-L77
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/PaddedDescent/F/RebalF.lean#L76-L77

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

theorem PaddedDescent.F.RebalF.halts_free {γ : Type} (q : α → γ) (f : γ → β) (a : α) : Halts (mapIn q (freeM f)) a (f (q a)) := by sorry
