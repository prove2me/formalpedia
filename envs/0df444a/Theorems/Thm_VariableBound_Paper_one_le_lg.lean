-- Prove2me | Theorems.Thm_VariableBound_Paper_one_le_lg
-- name    : VariableBound.Paper.one_le_lg
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-04T15:29:00.309657+00:00
-- url     : https://prove2.me/theorems/a024549f-003f-4e0d-9a36-ca300037012f
-- title:
--   Paper: one le lg
-- statement:
--   log m ≥ 1 for m ≥ 2.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/variables/VariableBound/Paper/Arith.lean#L55-L57
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/variables/VariableBound/Paper/Arith.lean#L55-L57

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

theorem VariableBound.Paper.one_le_lg {m : ℕ} (hm : 2 ≤ m) : 1 ≤ lg m := by sorry
