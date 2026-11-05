-- Prove2me | Theorems.Thm_PairsToBound_natCast_pow_eq
-- name    : PairsToBound.natCast_pow_eq
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-04T23:59:40.720865+00:00
-- url     : https://prove2.me/theorems/07a644c9-ab88-4049-97c1-61c806fa244e
-- title:
--   Pairs To Bound: nat Cast pow eq
-- statement:
--   n^j = 2^{j·log n} for n ≥ 1.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/variables/PairsToBound/Arith.lean#L186-L188
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/variables/PairsToBound/Arith.lean#L186-L188

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

theorem PairsToBound.natCast_pow_eq {n : ℕ} (hn : 1 ≤ n) (j : ℕ) : (n : ℝ) ^ j = (2 : ℝ) ^ ((j : ℝ) * lg n) := by sorry
