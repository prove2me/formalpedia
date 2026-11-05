-- Prove2me | Theorems.Thm_PairsToBound_mul_lglg_le_expN
-- name    : PairsToBound.mul_lglg_le_expN
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T01:22:47.569761+00:00
-- url     : https://prove2.me/theorems/4ca52b8b-467a-4023-a06f-d1b0e2cae223
-- title:
--   Pairs To Bound: mul lglg le exp N
-- statement:
--   «if k > (log n)^(1/4), then k²·n·log log n/√(log n) ≥ n·log log n», for n ≥ 4.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/variables/PairsToBound/Arith.lean#L128-L135
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/variables/PairsToBound/Arith.lean#L128-L135

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

theorem PairsToBound.mul_lglg_le_expN {k n : ℕ} (hn : 4 ≤ n) (h : lg n < (k : ℝ) ^ 4) : (n : ℝ) * lg (lg n) ≤ expN k n := by sorry
