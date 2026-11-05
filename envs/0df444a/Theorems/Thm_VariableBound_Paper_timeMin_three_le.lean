-- Prove2me | Theorems.Thm_VariableBound_Paper_timeMin_three_le
-- name    : VariableBound.Paper.timeMin_three_le
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-04T16:42:31.489242+00:00
-- url     : https://prove2.me/theorems/11b565b0-94f1-4210-bf5c-3657490a6c10
-- title:
--   Paper: time Min three le
-- statement:
--   At k = 3 the printed bound of Theorem 1 with the constant C is at most 2^{9C·min{m/√(log m),
--   n·log log n/√(log n)}}, for m ≥ 2 and n ≥ 4.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/variables/VariableBound/Paper/Arith.lean#L233-L246
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/variables/VariableBound/Paper/Arith.lean#L233-L246

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

theorem VariableBound.Paper.timeMin_three_le (C : ℕ) {m n : ℕ} (hm : 2 ≤ m) (hn : 4 ≤ n) : timeMin C 3 m n ≤ timeMin3 (9 * C) m n := by sorry
