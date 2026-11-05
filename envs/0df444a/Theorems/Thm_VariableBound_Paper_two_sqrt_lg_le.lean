-- Prove2me | Theorems.Thm_VariableBound_Paper_two_sqrt_lg_le
-- name    : VariableBound.Paper.two_sqrt_lg_le
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-04T16:02:57.178793+00:00
-- url     : https://prove2.me/theorems/99b5eeb0-9b35-4af7-964e-b00ac4b8d47b
-- title:
--   Paper: two sqrt lg le
-- statement:
--   2·√(log m) ≤ m for m ≥ 1.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/variables/VariableBound/Paper/Arith.lean#L70-L76
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/variables/VariableBound/Paper/Arith.lean#L70-L76

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

theorem VariableBound.Paper.two_sqrt_lg_le {m : ℕ} (hm : 1 ≤ m) : 2 * Real.sqrt (lg m) ≤ m := by sorry
