-- Prove2me | Theorems.Thm_ThmVariables_lg_lt
-- name    : ThmVariables.lg_lt
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T03:12:15.091059+00:00
-- url     : https://prove2.me/theorems/36022a8a-1892-43c6-b183-35ec5f5c11e4
-- title:
--   Thm Variables: lg lt
-- statement:
--   «log K > (log n)/(17C₀)»: for K, e, C₀ with the printed inequalities (`CliqueLevels.Levels`),
--   log n < 17·C₀·log K_ℓ at the level ℓ of n.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/variables/ThmVariables/Bound.lean#L74-L83
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/variables/ThmVariables/Bound.lean#L74-L83

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_ThmVariables_Defs
import Definitions.Def_RecursionToBound_Numbers
import Definitions.Def_VariableBound_Paper_Arith
import Definitions.Def_VariableBound_Printed_VariablesA_Arith
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.SpecialFunctions.Log.Base
import Mathlib.Order.Monotone.Basic
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring
import Mathlib.Tactic.NormNum
import Definitions.Def_ThmVariables_Bound
import Theorems.Thm_VariableBound_VariablesA_lg_lt

set_option autoImplicit false
section
section
open ThmVariables
open Turing CliqueLevels MainTheoremForms VariableBound.Paper
open Sat3 (CNF)
variable {K : ℕ → ℕ} {e : ℕ → ℝ} {C₀ : ℕ}

theorem ThmVariables.lg_lt (hL : Levels K e C₀) {n l : ℕ} (h : ThmVariables.IsLevel K n l) : lg n < 17 * C₀ * lg (K l) := by sorry
