-- Prove2me | Theorems.Thm_VariableBound_SmallBias_ip_zero_left
-- name    : VariableBound.SmallBias.ip_zero_left
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-04T17:34:27.684882+00:00
-- url     : https://prove2.me/theorems/25ee231a-145e-4682-890c-3d9c3300c309
-- title:
--   Small Bias: ip zero left
-- statement:
--   ⟨0, y⟩ = 0.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/variables/VariableBound/Family/SmallBias.lean#L61-L62
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/variables/VariableBound/Family/SmallBias.lean#L61-L62

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_AppVariablesStatement
import Mathlib.Algebra.Polynomial.Eval.Defs
import Mathlib.Algebra.Polynomial.Degree.Defs
import Mathlib.Algebra.Polynomial.Roots
import Mathlib.Algebra.Polynomial.BigOperators
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Data.ZMod.Basic
import Definitions.Def_VariableBound_Family_SmallBias
set_option autoImplicit false
section
section
open VariableBound VariableBound.SmallBias
open Finset AppVariables
variable {s : ℕ}

theorem VariableBound.SmallBias.ip_zero_left (y : Fin s → ZMod 2) : ip 0 y = 0 := by sorry
