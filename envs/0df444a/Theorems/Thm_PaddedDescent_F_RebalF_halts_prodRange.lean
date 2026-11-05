-- Prove2me | Theorems.Thm_PaddedDescent_F_RebalF_halts_prodRange
-- name    : PaddedDescent.F.RebalF.halts_prodRange
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T02:49:39.369023+00:00
-- url     : https://prove2.me/theorems/c8ec8299-f1cf-4df0-8027-5a118e6aaa82
-- title:
--   Rebal F: halts prod Range
-- statement:
--   The Rebal F construction uses the halts prod Range property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/PaddedDescent/F/RebalF.lean#L61-L66
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/PaddedDescent/F/RebalF.lean#L61-L66

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

theorem PaddedDescent.F.RebalF.halts_prodRange [HasSize α] {N : α → ℕ} {M : Stepped (α × ℕ) ℤ} {a : α} {v : ℕ → ℤ}
    (h : ∀ y, y < N a → Halts M (a, y) (v y)) : Halts (prodRange N M) a (∏ y ∈ range (N a), v y) := by sorry
