-- Prove2me | Theorems.Thm_ThmVariables_boundAtANumberBetween
-- name    : ThmVariables.boundAtANumberBetween
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T01:26:35.055549+00:00
-- url     : https://prove2.me/theorems/fb6301f7-a99f-4f14-888b-26f2f33e1474
-- title:
--   Thm Variables: bound At ANumber Between
-- statement:
--   The bound at a number in [e, 2e] is the bound at e with twice the constant: for 0 < e ≤ e′ ≤ 2e,
--   e′ ≤ 1 and k ≥ 1, 2^{C·k²·e′·n·log(k/e′)} ≤ 2^{2C·k²·e·n·log(k/e)}, both rounded down.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/variables/ThmVariables/Bound.lean#L100-L106
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/variables/ThmVariables/Bound.lean#L100-L106

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
set_option autoImplicit false
section
section
open ThmVariables
open Turing CliqueLevels MainTheoremForms VariableBound.Paper
open Sat3 (CNF)
variable {K : ℕ → ℕ} {e : ℕ → ℝ} {C₀ : ℕ}

theorem ThmVariables.boundAtANumberBetween : BoundAtANumberBetween := by sorry
