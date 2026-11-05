-- Prove2me | Theorems.Thm_PairsToBound_two_rpow_mono
-- name    : PairsToBound.two_rpow_mono
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T00:13:39.836141+00:00
-- url     : https://prove2.me/theorems/c26752f9-9f9d-4e73-83b4-fec00a604ffa
-- title:
--   Pairs To Bound: two rpow mono
-- statement:
--   2^{a·X} ≤ 2^{b·X} for natural numbers a ≤ b and X ≥ 0.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/variables/PairsToBound/Arith.lean#L191-L192
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/variables/PairsToBound/Arith.lean#L191-L192

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

theorem PairsToBound.two_rpow_mono {a b : ℕ} (h : a ≤ b) {X : ℝ} (hX : 0 ≤ X) : (2 : ℝ) ^ ((a : ℝ) * X) ≤ (2 : ℝ) ^ ((b : ℝ) * X) := by sorry
