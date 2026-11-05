-- Prove2me | Theorems.Thm_VariableBound_Paper_two_le_expN
-- name    : VariableBound.Paper.two_le_expN
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-04T15:29:20.544984+00:00
-- url     : https://prove2.me/theorems/42d921bd-7e52-4544-ac9e-1607fec5ef60
-- title:
--   Paper: two le exp N
-- statement:
--   k²·n·log log n/√(log n) ≥ 2 for k ≥ 1 and n ≥ 4.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/variables/VariableBound/Paper/Arith.lean#L137-L142
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/variables/VariableBound/Paper/Arith.lean#L137-L142

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

theorem VariableBound.Paper.two_le_expN {k n : ℕ} (hk : 1 ≤ k) (hn : 4 ≤ n) : 2 ≤ expN k n := by sorry
