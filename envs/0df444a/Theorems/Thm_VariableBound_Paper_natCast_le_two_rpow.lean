-- Prove2me | Theorems.Thm_VariableBound_Paper_natCast_le_two_rpow
-- name    : VariableBound.Paper.natCast_le_two_rpow
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-04T15:30:03.411736+00:00
-- url     : https://prove2.me/theorems/2a0ccaa0-b262-4890-a8b4-7a3520502878
-- title:
--   Paper: nat Cast le two rpow
-- statement:
--   C ≤ 2^{C·X} for X ≥ 1.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/variables/VariableBound/Paper/Arith.lean#L176-L180
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/variables/VariableBound/Paper/Arith.lean#L176-L180

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

theorem VariableBound.Paper.natCast_le_two_rpow (C : ℕ) {X : ℝ} (hX : 1 ≤ X) : (C : ℝ) ≤ (2 : ℝ) ^ ((C : ℝ) * X) := by sorry
