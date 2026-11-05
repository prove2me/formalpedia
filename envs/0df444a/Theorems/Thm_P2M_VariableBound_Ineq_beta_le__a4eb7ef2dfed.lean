-- Prove2me | Theorems.Thm_P2M_VariableBound_Ineq_beta_le__a4eb7ef2dfed
-- name    : P2M_VariableBound_Ineq_beta_le__a4eb7ef2dfed
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-04T16:52:38.903192+00:00
-- url     : https://prove2.me/theorems/78975611-22a4-4d88-8b83-02fccc9309c7
-- title:
--   P2 M Variable Bound Ineq beta le  a4eb7ef2dfed: P2 M Variable Bound Ineq beta le  a4eb7ef2dfed
-- statement:
--   n + 3(n̄+1)·log(2Δ) + 2 ≤ 4n + 3·log(2Δ) + 2, for Δ ≥ 1.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/variables/VariableBound/Params/Ineq.lean#L122-L124
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/variables/VariableBound/Params/Ineq.lean#L122-L124

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

theorem P2M_VariableBound_Ineq_beta_le__a4eb7ef2dfed {n Δ nb : ℕ} (hΔ : 1 ≤ Δ) (h : IsNb n Δ nb) : (n : ℝ) + 3 * (nb + 1) * lg (2 * Δ) + 2 ≤ 4 * n + 3 * lg (2 * Δ) + 2 := by sorry

alias «VariableBound».«Ineq».«beta_le₂» := P2M_VariableBound_Ineq_beta_le__a4eb7ef2dfed
