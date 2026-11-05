-- Prove2me | Theorems.Thm_VariableBound_Ineq_large
-- name    : VariableBound.Ineq.large
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-04T16:55:19.6016+00:00
-- url     : https://prove2.me/theorems/a2c8c44e-4dd1-4177-a586-36599213e4a6
-- title:
--   Ineq: large
-- statement:
--   The bounds for large n: r̄ ≤ 10n and M ≤ 14n for the β, r̄ and M of the text, for 2 ≤ Δ, n̄ < m
--   ≤ Δ·n and n ≥ 29·log(2Δ) + 19.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/variables/VariableBound/Params/Ineq.lean#L148-L164
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/variables/VariableBound/Params/Ineq.lean#L148-L164

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

theorem VariableBound.Ineq.large {n Δ m nb rb : ℕ} (hΔ : 2 ≤ Δ) (hnm : nb < m) (hm : m ≤ Δ * n) (h : IsNb n Δ nb) (hr : IsRb (beta n m nb) rb)
    (hn : 29 * lg (2 * Δ) + 19 ≤ n) : rb ≤ 10 * n ∧ Mb (beta n m nb) rb ≤ 14 * n := by sorry
