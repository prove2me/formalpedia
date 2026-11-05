-- Prove2me | Theorems.Thm_PairsToBound_main_case_le
-- name    : PairsToBound.main_case_le
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T03:11:28.576443+00:00
-- url     : https://prove2.me/theorems/33d2402d-105e-4938-a87a-946bea5abbdd
-- title:
--   Pairs To Bound: main case le
-- statement:
--   The branch of the main regime, as numbers: for k ≥ 1, n ≥ 4, k′² ≤ 9k², len + 1 ≤ (n+2)^(5k) and
--   c₁ at least 9C₁ and at least 10, q·(2^{C₁·k′²·n·log log n/√(log n)} + len + 1)^q ≤
--   2^{q(c₁+2)·k²·n·log log n/√(log n)}, both powers of 2 rounded down.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/variables/PairsToBound/Arith.lean#L237-L247
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/variables/PairsToBound/Arith.lean#L237-L247

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

theorem PairsToBound.main_case_le (q C₁ c₁ : ℕ) (h1 : 9 * C₁ ≤ c₁) (h2 : 10 ≤ c₁) {k k' n len : ℕ} (hk : 1 ≤ k) (hn : 4 ≤ n) (hkk : k' ^ 2 ≤ 9 * k ^ 2) (hlen : len + 1 ≤ (n + 2) ^ (5 * k)) :
    q * (timeN C₁ k' n + len + 1) ^ q ≤ timeN (q * (c₁ + 2)) k n := by sorry
