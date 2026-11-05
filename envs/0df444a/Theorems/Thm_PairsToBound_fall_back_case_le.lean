-- Prove2me | Theorems.Thm_PairsToBound_fall_back_case_le
-- name    : PairsToBound.fall_back_case_le
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T03:12:38.516167+00:00
-- url     : https://prove2.me/theorems/81b1f463-5c2d-4232-9d84-4bc5b3d8b5be
-- title:
--   Pairs To Bound: fall back case le
-- statement:
--   The branch that tries all assignments, as numbers: for k ≥ 1, n ≥ 4, n ≤ D·k²·n·log log n/√(log
--   n), len + 1 ≤ (n+2)^(5k) and c₁ at least c(D+1) and at least 10, q·(2^{c·n}·n^{c·k} + len + 1)^q ≤
--   2^{q(c₁+2)·k²·n·log log n/√(log n)}, rounded down.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/variables/PairsToBound/Arith.lean#L252-L266
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/variables/PairsToBound/Arith.lean#L252-L266

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

theorem PairsToBound.fall_back_case_le (q c D c₁ : ℕ) (h1 : c * (D + 1) ≤ c₁) (h2 : 10 ≤ c₁) {k n len : ℕ} (hk : 1 ≤ k) (hn : 4 ≤ n) (hD : (n : ℝ) ≤ (D : ℝ) * expN k n) (hlen : len + 1 ≤ (n + 2) ^ (5 * k)) :
    q * (2 ^ (c * n) * n ^ (c * k) + len + 1) ^ q ≤ timeN (q * (c₁ + 2)) k n := by sorry
