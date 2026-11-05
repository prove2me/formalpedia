-- Prove2me | Theorems.Thm_VariableBound_Paper_two_le_expM
-- name    : VariableBound.Paper.two_le_expM
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-04T15:29:11.268353+00:00
-- url     : https://prove2.me/theorems/57921f9a-af22-404e-a868-3d46065241aa
-- title:
--   Paper: two le exp M
-- statement:
--   k·m/√(log m) ≥ 2 for k ≥ 1 and m ≥ 2.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/variables/VariableBound/Paper/Arith.lean#L108-L115
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/variables/VariableBound/Paper/Arith.lean#L108-L115

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

theorem VariableBound.Paper.two_le_expM {k m : ℕ} (hk : 1 ≤ k) (hm : 2 ≤ m) : 2 ≤ expM k m := by sorry
