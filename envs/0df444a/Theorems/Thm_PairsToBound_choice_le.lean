-- Prove2me | Theorems.Thm_PairsToBound_choice_le
-- name    : PairsToBound.choice_le
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T00:13:43.690764+00:00
-- url     : https://prove2.me/theorems/4183c79d-ee3a-45e4-9356-58b659e57b05
-- title:
--   Pairs To Bound: choice le
-- statement:
--   The polynomial factor q·(t + len + 1)^q goes into the constant: if t ≤ 2^{c₁·X}, len + 1 ≤
--   2^{c₁·X} and X ≥ 1, then q·(t + len + 1)^q ≤ 2^{q(c₁+2)·X}, rounded down.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/variables/PairsToBound/Arith.lean#L196-L218
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/variables/PairsToBound/Arith.lean#L196-L218

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

theorem PairsToBound.choice_le (q c₁ : ℕ) {t len : ℕ} {X : ℝ} (hX : 1 ≤ X) (ht : (t : ℝ) ≤ (2 : ℝ) ^ ((c₁ : ℝ) * X)) (hl : ((len + 1 : ℕ) : ℝ) ≤ (2 : ℝ) ^ ((c₁ : ℝ) * X)) :
    q * (t + len + 1) ^ q ≤ ⌊(2 : ℝ) ^ (((q * (c₁ + 2) : ℕ) : ℝ) * X)⌋₊ := by sorry
