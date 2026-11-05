-- Prove2me | Theorems.Thm_ThmVariables_inParticular
-- name    : ThmVariables.inParticular
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T03:15:17.191274+00:00
-- url     : https://prove2.me/theorems/96cdfa8e-e737-4021-af10-2560a5565a3f
-- title:
--   Thm Variables: in Particular
-- statement:
--   «In particular, if e_ℓ = O((log K_ℓ)^(−α′)) for a constant α′ > 0, the time is 2^{O(k²·n·log log
--   n/(log n)^α′)}» (Theorem D (a)), for every machine with the bound of Theorem D (a).
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/variables/ThmVariables/Bound.lean#L112-L160
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/variables/ThmVariables/Bound.lean#L112-L160

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

theorem ThmVariables.inParticular : InParticular := by sorry
