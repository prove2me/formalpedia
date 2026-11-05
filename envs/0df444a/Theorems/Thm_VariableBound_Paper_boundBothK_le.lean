-- Prove2me | Theorems.Thm_VariableBound_Paper_boundBothK_le
-- name    : VariableBound.Paper.boundBothK_le
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-04T16:42:27.945964+00:00
-- url     : https://prove2.me/theorems/0b85bf37-46c1-48b8-8c81-820e9baccce3
-- title:
--   Paper: bound Both K le
-- statement:
--   For k ≥ 1, m ≥ 2 and n ≥ 4 the bound with the minimum of `UniformInKStatement.lean` with the
--   constant C is at most the printed bound of Theorem 1 with the constant 3C.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/variables/VariableBound/Paper/Arith.lean#L204-L213
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/variables/VariableBound/Paper/Arith.lean#L204-L213

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

theorem VariableBound.Paper.boundBothK_le (C : ℕ) {k m n : ℕ} (hk : 1 ≤ k) (hm : 2 ≤ m) (hn : 4 ≤ n) :
    SatM.boundBothK (SatK.rN 1 (1 / 2)) (SatM.rPow (1 / 2)) C k n m ≤ timeMin (3 * C) k m n := by sorry
