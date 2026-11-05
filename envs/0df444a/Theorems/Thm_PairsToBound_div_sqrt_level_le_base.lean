-- Prove2me | Theorems.Thm_PairsToBound_div_sqrt_level_le_base
-- name    : PairsToBound.div_sqrt_level_le_base
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T01:22:55.727487+00:00
-- url     : https://prove2.me/theorems/4445f325-246b-4891-9063-7b88e154eb82
-- title:
--   Pairs To Bound: div sqrt level le base
-- statement:
--   «and if n < K₀^17, then n·log log n/√(log n) ≥ n/√(17·log K₀)», for n ≥ 4.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/variables/PairsToBound/Arith.lean#L138-L148
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/variables/PairsToBound/Arith.lean#L138-L148

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

theorem PairsToBound.div_sqrt_level_le_base {K₀ n : ℕ} (hn : 4 ≤ n) (h : n < K₀ ^ 17) : (n : ℝ) / Real.sqrt (17 * lg K₀) ≤ n * lg (lg n) / Real.sqrt (lg n) := by sorry
