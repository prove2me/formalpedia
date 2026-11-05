-- Prove2me | Theorems.Thm_VariableBound_Paper_shiftM_le
-- name    : VariableBound.Paper.shiftM_le
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-04T15:39:55.525009+00:00
-- url     : https://prove2.me/theorems/c30effdb-1472-46e4-a661-df257fd60f5e
-- title:
--   Paper: shift M le
-- statement:
--   k·m/√(log₂(m+2)) ≤ k·m/√(log m) for m ≥ 2.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/variables/VariableBound/Paper/Arith.lean#L147-L154
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/variables/VariableBound/Paper/Arith.lean#L147-L154

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

theorem VariableBound.Paper.shiftM_le (k : ℕ) {m : ℕ} (hm : 2 ≤ m) : (k : ℝ) * m * SatM.rPow (1 / 2) m ≤ expM k m := by sorry
