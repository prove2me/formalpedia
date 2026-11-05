-- Prove2me | Theorems.Thm_VariableBound_Paper_expM_eq
-- name    : VariableBound.Paper.expM_eq
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-04T16:02:55.985194+00:00
-- url     : https://prove2.me/theorems/8167856d-f40a-465e-b4e1-aa86a2685933
-- title:
--   Paper: exp M eq
-- statement:
--   The exponent in m is k times m/√(log m).
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/variables/VariableBound/Paper/Arith.lean#L132-L134
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/variables/VariableBound/Paper/Arith.lean#L132-L134

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

theorem VariableBound.Paper.expM_eq (k m : ℕ) : expM k m = (k : ℝ) * ((m : ℝ) / Real.sqrt (lg m)) := by sorry
