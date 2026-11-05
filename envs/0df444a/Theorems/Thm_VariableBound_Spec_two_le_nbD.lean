-- Prove2me | Theorems.Thm_VariableBound_Spec_two_le_nbD
-- name    : VariableBound.Spec.two_le_nbD
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-04T17:40:35.287084+00:00
-- url     : https://prove2.me/theorems/f44953ec-809f-4d93-9a3c-ab151778aefb
-- title:
--   Spec: two le nb D
-- statement:
--   The computed n̄ is at least 2, if Δ ≥ 1 and (2Δ)² ≤ 2^n.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/variables/VariableBound/Params/Spec.lean#L93-L104
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/variables/VariableBound/Params/Spec.lean#L93-L104

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

theorem VariableBound.Spec.two_le_nbD (n Δ : ℕ) (hΔ : 1 ≤ Δ) (h : (2 * Δ) ^ 2 ≤ 2 ^ n) : 2 ≤ nbD n Δ := by sorry
