-- Prove2me | Theorems.Thm_VariableBound_Spec_tb_iff
-- name    : VariableBound.Spec.tb_iff
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-04T17:40:52.086352+00:00
-- url     : https://prove2.me/theorems/17cac341-b34b-45c1-a06c-2f1a8ef9b5e0
-- title:
--   Spec: tb iff
-- statement:
--   The condition on c in the definition of t̄, with the denominators cleared; for n̄ ≥ 1.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/variables/VariableBound/Params/Spec.lean#L122-L130
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/variables/VariableBound/Params/Spec.lean#L122-L130

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

theorem VariableBound.Spec.tb_iff (m nb rb c : ℕ) (hnb : 1 ≤ nb) : (m : ℚ) * (1 + pp nb) ^ rb ≤ 2 ^ c ↔ m * (15 * nb + 16) ^ rb ≤ 2 ^ c * (15 * nb) ^ rb := by sorry
