-- Prove2me | Theorems.Thm_PairsToBound_le_of_wide
-- name    : PairsToBound.le_of_wide
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T03:10:58.837072+00:00
-- url     : https://prove2.me/theorems/602da10a-4c40-4e68-b625-e0d5d9f1864b
-- title:
--   Pairs To Bound: le of wide
-- statement:
--   If the width k′ used by the algorithm exceeds (log n)^(1/4) and k′² ≤ 9k², then n ≤ 9·k²·n·log
--   log n/√(log n).
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/variables/PairsToBound/Arith.lean#L169-L170
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/variables/PairsToBound/Arith.lean#L169-L170

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_PairsToBound_Defs
import Definitions.Def_VariableBound_Paper_Arith
import Definitions.Def_VariableBound_Printed_VariablesA_StepSparsify
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.SpecialFunctions.Log.Base
import Mathlib.Analysis.SpecialFunctions.Log.Deriv
import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.Analysis.SpecialFunctions.Exponential
import Mathlib.Analysis.Complex.ExponentialBounds
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring
import Mathlib.Tactic.NormNum
import Definitions.Def_PairsToBound_Arith
set_option autoImplicit false
section
section
open PairsToBound
open MainTheoremForms VariableBound.Paper

theorem PairsToBound.le_of_wide {k k' n : ℕ} (hn : 4 ≤ n) (h : lg n < (k' : ℝ) ^ 4) (hk : k' ^ 2 ≤ 9 * k ^ 2) : (n : ℝ) ≤ 9 * expN k n := by sorry
