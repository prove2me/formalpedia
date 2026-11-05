-- Prove2me | Theorems.Thm_VariableBound_SmallBias_half_strings
-- name    : VariableBound.SmallBias.half_strings
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-04T17:35:00.791227+00:00
-- url     : https://prove2.me/theorems/779adfbf-f39f-4686-96a9-a248d44d4de7
-- title:
--   Small Bias: half strings
-- statement:
--   For a string x ≠ 0, exactly half of the strings y of s bits have ⟨x, y⟩ = 1: if x_i = 1, then y
--   ↦ y + e_i exchanges the y with ⟨x, y⟩ = 1 and the others.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/variables/VariableBound/Family/SmallBias.lean#L70-L82
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/variables/VariableBound/Family/SmallBias.lean#L70-L82

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

theorem VariableBound.SmallBias.half_strings (x : Fin s → ZMod 2) (hx : x ≠ 0) : 2 * #{y : Fin s → ZMod 2 | ip x y = 1} = Fintype.card (Fin s → ZMod 2) := by sorry
