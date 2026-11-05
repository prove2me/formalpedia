-- Prove2me | Theorems.Thm_VariableBound_Ineq_tb_le
-- name    : VariableBound.Ineq.tb_le
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-04T16:55:35.29023+00:00
-- url     : https://prove2.me/theorems/d038753d-0c59-44b5-a7d7-f9a0a48203c8
-- title:
--   Ineq: tb le
-- statement:
--   t̄ ≤ log m + 33·log(2Δ) + 1 for the t̄ of the text (`IsTb m n̄ r̄ t̄`), for 2 ≤ Δ, m ≥ 1 and any
--   number r̄ ≤ 10n.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/variables/VariableBound/Params/Ineq.lean#L189-L211
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/variables/VariableBound/Params/Ineq.lean#L189-L211

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_VariableBound_Params_Defs
import Definitions.Def_ClauseBound_ParityChecks_Binom
import Mathlib.Analysis.SpecialFunctions.Log.Deriv
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import Definitions.Def_VariableBound_Params_Ineq
set_option autoImplicit false
section
section
open VariableBound
open AppVariables
open VariableBound.Ineq

theorem VariableBound.Ineq.tb_le {n Δ m nb rb tb : ℕ} (hΔ : 2 ≤ Δ) (hm : 1 ≤ m) (h : IsNb n Δ nb) (hr : rb ≤ 10 * n) (ht : IsTb m nb rb tb) :
    (tb : ℝ) ≤ lg m + 33 * lg (2 * Δ) + 1 := by sorry
