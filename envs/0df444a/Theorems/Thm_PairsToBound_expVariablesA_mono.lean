-- Prove2me | Theorems.Thm_PairsToBound_expVariablesA_mono
-- name    : PairsToBound.expVariablesA_mono
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T01:22:46.614651+00:00
-- url     : https://prove2.me/theorems/fb484829-5b02-4eee-a593-9f8b0a2c07ab
-- title:
--   Pairs To Bound: exp Variables A mono
-- statement:
--   For 3 ≤ k ≤ k′ and 0 < e ≤ 1: k²·e·n·log(k/e) is at most the same number at k′.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/variables/PairsToBound/Arith.lean#L68-L75
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/variables/PairsToBound/Arith.lean#L68-L75

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

theorem PairsToBound.expVariablesA_mono {k k' n : ℕ} {e : ℝ} (hk : 3 ≤ k) (h : k ≤ k') (he : 0 < e) (he1 : e ≤ 1) : expVariablesA k n e ≤ expVariablesA k' n e := by sorry
