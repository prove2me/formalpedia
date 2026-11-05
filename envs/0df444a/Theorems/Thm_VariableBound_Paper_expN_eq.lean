-- Prove2me | Theorems.Thm_VariableBound_Paper_expN_eq
-- name    : VariableBound.Paper.expN_eq
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-04T15:32:15.298168+00:00
-- url     : https://prove2.me/theorems/27090f58-04a1-4abd-90eb-8d2d3590ab94
-- title:
--   Paper: exp N eq
-- statement:
--   The exponent in n is k² times n·log log n/√(log n).
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/variables/VariableBound/Paper/Arith.lean#L127-L129
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/variables/VariableBound/Paper/Arith.lean#L127-L129

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_MainTheoremFormsStatement
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.SpecialFunctions.Log.Base
import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.FieldSimp
import Definitions.Def_VariableBound_Paper_Arith
set_option autoImplicit false
section
section
open VariableBound VariableBound.Paper
open MainTheoremForms

theorem VariableBound.Paper.expN_eq (k n : ℕ) : expN k n = (k : ℝ) ^ 2 * ((n : ℝ) * lg (lg n) / Real.sqrt (lg n)) := by sorry
