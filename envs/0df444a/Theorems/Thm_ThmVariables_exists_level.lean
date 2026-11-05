-- Prove2me | Theorems.Thm_ThmVariables_exists_level
-- name    : ThmVariables.exists_level
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T03:14:08.35406+00:00
-- url     : https://prove2.me/theorems/36449743-e180-4586-8aad-4abadf3ecaab
-- title:
--   Thm Variables: exists level
-- statement:
--   For K, e, C₀ with the printed inequalities (`CliqueLevels.Levels`), every n ≥ K₀^17 has a level:
--   an ℓ with K_ℓ^17 ≤ n < K_(ℓ+1)^17.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/variables/ThmVariables/Bound.lean#L47-L54
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/variables/ThmVariables/Bound.lean#L47-L54

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

theorem ThmVariables.exists_level (hL : Levels K e C₀) {n : ℕ} (hn : K 0 ^ 17 ≤ n) : ∃ l, ThmVariables.IsLevel K n l := by sorry
