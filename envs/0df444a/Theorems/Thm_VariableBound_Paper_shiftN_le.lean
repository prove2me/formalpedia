-- Prove2me | Theorems.Thm_VariableBound_Paper_shiftN_le
-- name    : VariableBound.Paper.shiftN_le
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-04T16:02:58.148102+00:00
-- url     : https://prove2.me/theorems/aff7885a-a439-4b7b-b2cc-59be4c53d244
-- title:
--   Paper: shift N le
-- statement:
--   k²·n·log₂ log₂(n+4)/√(log₂(n+4)) ≤ 2·k²·n·log log n/√(log n) for n ≥ 4.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/variables/VariableBound/Paper/Arith.lean#L157-L171
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/variables/VariableBound/Paper/Arith.lean#L157-L171

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

theorem VariableBound.Paper.shiftN_le (k : ℕ) {n : ℕ} (hn : 4 ≤ n) : (k : ℝ) ^ 2 * n * SatK.rN 1 (1 / 2) n ≤ 2 * expN k n := by sorry
