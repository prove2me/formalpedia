-- Prove2me | Theorems.Thm_PairsToBound_le_of_small
-- name    : PairsToBound.le_of_small
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T03:10:58.508997+00:00
-- url     : https://prove2.me/theorems/02d6523a-253c-4d3d-905f-f3bd3e2b2468
-- title:
--   Pairs To Bound: le of small
-- statement:
--   If n < K₀^17 and √(17·log K₀) ≤ D, then n ≤ D·k²·n·log log n/√(log n), for k ≥ 1, K₀ ≥ 2 and n ≥ 4.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/variables/PairsToBound/Arith.lean#L173-L183
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/variables/PairsToBound/Arith.lean#L173-L183

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

theorem PairsToBound.le_of_small {K₀ k n : ℕ} {D : ℝ} (hK : 2 ≤ K₀) (hk : 1 ≤ k) (hn : 4 ≤ n) (h : n < K₀ ^ 17) (hD : Real.sqrt (17 * lg K₀) ≤ D) : (n : ℝ) ≤ D * expN k n := by sorry
