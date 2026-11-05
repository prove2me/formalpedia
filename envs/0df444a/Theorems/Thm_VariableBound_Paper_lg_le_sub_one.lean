-- Prove2me | Theorems.Thm_VariableBound_Paper_lg_le_sub_one
-- name    : VariableBound.Paper.lg_le_sub_one
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-04T15:36:39.694949+00:00
-- url     : https://prove2.me/theorems/a835e35f-925c-482f-bb00-3f643090bcad
-- title:
--   Paper: lg le sub one
-- statement:
--   log m ≤ m − 1 for m ≥ 1.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/variables/VariableBound/Paper/Arith.lean#L60-L67
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/variables/VariableBound/Paper/Arith.lean#L60-L67

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

theorem VariableBound.Paper.lg_le_sub_one {m : ℕ} (hm : 1 ≤ m) : lg m ≤ (m : ℝ) - 1 := by sorry
