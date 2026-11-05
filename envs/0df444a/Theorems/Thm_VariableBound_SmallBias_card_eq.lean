-- Prove2me | Theorems.Thm_VariableBound_SmallBias_card_eq
-- name    : VariableBound.SmallBias.card_eq
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-04T17:35:20.09223+00:00
-- url     : https://prove2.me/theorems/4280e5d3-9def-47f2-99c7-9a7f9b74627d
-- title:
--   Small Bias: card eq
-- statement:
--   A field whose elements are written, by `bits`, as the strings of s bits has 2^s elements.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/variables/VariableBound/Family/SmallBias.lean#L173-L174
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/variables/VariableBound/Family/SmallBias.lean#L173-L174

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
variable {F : Type} [Field F] [Fintype F] [Algebra (ZMod 2) F] {s : ℕ}

theorem VariableBound.SmallBias.card_eq (bits : F ≃ₗ[ZMod 2] (Fin s → ZMod 2)) : Fintype.card F = 2 ^ s := by sorry
