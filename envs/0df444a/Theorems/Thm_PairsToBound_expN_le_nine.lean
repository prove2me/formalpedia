-- Prove2me | Theorems.Thm_PairsToBound_expN_le_nine
-- name    : PairsToBound.expN_le_nine
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T01:22:50.335908+00:00
-- url     : https://prove2.me/theorems/e839f170-eab3-47a2-a216-2065108b2dba
-- title:
--   Pairs To Bound: exp N le nine
-- statement:
--   «which multiplies k² by at most 9»: if k′² ≤ 9k², the exponent at k′ is at most 9 times that at
--   k, for n ≥ 4.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/variables/PairsToBound/Arith.lean#L160-L165
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/variables/PairsToBound/Arith.lean#L160-L165

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

theorem PairsToBound.expN_le_nine {k k' n : ℕ} (hn : 4 ≤ n) (h : k' ^ 2 ≤ 9 * k ^ 2) : expN k' n ≤ 9 * expN k n := by sorry
