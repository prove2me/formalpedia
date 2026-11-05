-- Prove2me | Theorems.Thm_VariableBound_Spec_isRb_rbD
-- name    : VariableBound.Spec.isRb_rbD
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-04T17:40:41.29818+00:00
-- url     : https://prove2.me/theorems/d3035e79-1d54-4af2-aaa4-d4883e009f19
-- title:
--   Spec: is Rb rb D
-- statement:
--   The computed r̄ is the r̄ of the text.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/variables/VariableBound/Params/Spec.lean#L107-L119
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/variables/VariableBound/Params/Spec.lean#L107-L119

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

theorem VariableBound.Spec.isRb_rbD (β : ℕ) : IsRb β (rbD β) := by sorry
