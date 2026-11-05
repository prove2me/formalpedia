-- Prove2me | Theorems.Thm_VariableBound_SmallBias_ip_single
-- name    : VariableBound.SmallBias.ip_single
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-04T17:35:00.391739+00:00
-- url     : https://prove2.me/theorems/cc738fa8-52e1-4a36-b920-99b532a44be9
-- title:
--   Small Bias: ip single
-- statement:
--   ⟨x, e_i⟩ = x_i for the string e_i with the single bit 1 at place i.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/variables/VariableBound/Family/SmallBias.lean#L65-L66
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/variables/VariableBound/Family/SmallBias.lean#L65-L66

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

theorem VariableBound.SmallBias.ip_single (x : Fin s → ZMod 2) (i : Fin s) : ip x (Pi.single i 1) = x i := by sorry
