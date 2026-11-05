-- Prove2me | Theorems.Thm_VariableBound_Spec_nb_count
-- name    : VariableBound.Spec.nb_count
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-04T16:53:30.785124+00:00
-- url     : https://prove2.me/theorems/aedc155f-c613-4666-b380-fe6bc7249dea
-- title:
--   Spec: nb count
-- statement:
--   What `count_spec` gives for n̄: the count a of `nbD` is the least number with 2^n < (2Δ)^(2^a),
--   for Δ ≥ 1.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/variables/VariableBound/Params/Spec.lean#L68-L77
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/variables/VariableBound/Params/Spec.lean#L68-L77

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_VariableBound_Params_Defs
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Ring
import Definitions.Def_VariableBound_Params_Spec
set_option autoImplicit false
section
section
open VariableBound
open AppVariables
open VariableBound.Spec

theorem VariableBound.Spec.nb_count (n Δ : ℕ) (hΔ : 1 ≤ Δ) :
    2 ^ n < (2 * Δ) ^ 2 ^ ((List.range (Nat.log 2 n + 1)).filter fun a => decide ((2 * Δ) ^ 2 ^ a ≤ 2 ^ n)).length ∧
      ∀ a < ((List.range (Nat.log 2 n + 1)).filter fun a => decide ((2 * Δ) ^ 2 ^ a ≤ 2 ^ n)).length, (2 * Δ) ^ 2 ^ a ≤ 2 ^ n := by sorry
