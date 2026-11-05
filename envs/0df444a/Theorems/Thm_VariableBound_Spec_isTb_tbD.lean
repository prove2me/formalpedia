-- Prove2me | Theorems.Thm_VariableBound_Spec_isTb_tbD
-- name    : VariableBound.Spec.isTb_tbD
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-04T17:41:01.340481+00:00
-- url     : https://prove2.me/theorems/6e1a21b7-4834-4d58-a00b-eaee0c83671d
-- title:
--   Spec: is Tb tb D
-- statement:
--   The computed t̄ is the t̄ of the text, if n̄ ≥ 2.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/variables/VariableBound/Params/Spec.lean#L133-L141
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/variables/VariableBound/Params/Spec.lean#L133-L141

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

theorem VariableBound.Spec.isTb_tbD (m nb rb : ℕ) (hnb : 2 ≤ nb) : IsTb m nb rb (tbD m nb rb) := by sorry
