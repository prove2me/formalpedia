-- Prove2me | Theorems.Thm_ThmVariables_expVariablesA_le_two_mul
-- name    : ThmVariables.expVariablesA_le_two_mul
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T03:15:24.23333+00:00
-- url     : https://prove2.me/theorems/ed8f5a9c-16b6-4c41-be23-9b37b360a984
-- title:
--   Thm Variables: exp Variables A le two mul
-- statement:
--   For 0 < e ≤ e′ ≤ 2e, e′ ≤ 1 ≤ k: k²·e′·n·log(k/e′) ≤ 2·k²·e·n·log(k/e).
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/variables/ThmVariables/Bound.lean#L88-L96
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/variables/ThmVariables/Bound.lean#L88-L96

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

theorem ThmVariables.expVariablesA_le_two_mul {k n : ℕ} {e e' : ℝ} (hk : 1 ≤ k) (he : 0 < e) (h1 : e ≤ e') (h2 : e' ≤ 2 * e) (h3 : e' ≤ 1) : expVariablesA k n e' ≤ 2 * expVariablesA k n e := by sorry
