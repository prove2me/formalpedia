-- Prove2me | Theorems.Thm_VariableBound_SmallBias_eval_poly
-- name    : VariableBound.SmallBias.eval_poly
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-04T17:35:14.968902+00:00
-- url     : https://prove2.me/theorems/562825ad-98e6-4e75-b824-e2c3ab226f25
-- title:
--   Small Bias: eval poly
-- statement:
--   The value of the polynomial at u₃ is w = Σ_{E ∈ V′} u₃^ι(E); at u₃ = 0 the power with exponent 0
--   is 1.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/variables/VariableBound/Family/SmallBias.lean#L130-L131
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/variables/VariableBound/Family/SmallBias.lean#L130-L131

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
variable {F : Type} [Field F] {m : ℕ}

theorem VariableBound.SmallBias.eval_poly (V' : Finset (Fin m)) (u₃ : F) : (poly F V').eval u₃ = ∑ E ∈ V', u₃ ^ E.val := by sorry
