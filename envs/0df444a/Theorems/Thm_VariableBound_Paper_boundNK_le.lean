-- Prove2me | Theorems.Thm_VariableBound_Paper_boundNK_le
-- name    : VariableBound.Paper.boundNK_le
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-04T16:42:29.456349+00:00
-- url     : https://prove2.me/theorems/d3a56ad5-a2d6-4d79-b2c4-477958d7193d
-- title:
--   Paper: bound NK le
-- statement:
--   For k ≥ 1 and n ≥ 4 the bound in n of `UniformInKStatement.lean` with the constant C is at most
--   the printed bound of Theorem D (b) with the constant 3C.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/variables/VariableBound/Paper/Arith.lean#L195-L200
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/variables/VariableBound/Paper/Arith.lean#L195-L200

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

theorem VariableBound.Paper.boundNK_le (C : ℕ) {k n : ℕ} (hk : 1 ≤ k) (hn : 4 ≤ n) : SatM.boundNK (SatK.rN 1 (1 / 2)) C k n ≤ timeN (3 * C) k n := by sorry
