-- Prove2me | Theorems.Thm_VariableBound_Paper_absorb
-- name    : VariableBound.Paper.absorb
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-04T15:36:52.801467+00:00
-- url     : https://prove2.me/theorems/2c463b11-8d84-4d2a-8b6c-3807e28e74cc
-- title:
--   Paper: absorb
-- statement:
--   If E ≤ 2·X and X ≥ 1, then C·2^{C·E} ≤ 2^{3C·X}.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/variables/VariableBound/Paper/Arith.lean#L183-L191
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/variables/VariableBound/Paper/Arith.lean#L183-L191

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

theorem VariableBound.Paper.absorb (C : ℕ) {E X : ℝ} (hE : E ≤ 2 * X) (hX : 1 ≤ X) : (C : ℝ) * (2 : ℝ) ^ ((C : ℝ) * E) ≤ (2 : ℝ) ^ (((3 * C : ℕ) : ℝ) * X) := by sorry
