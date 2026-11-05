-- Prove2me | Theorems.Thm_VariableBound_Paper_lg_add_four
-- name    : VariableBound.Paper.lg_add_four
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-04T15:29:14.366195+00:00
-- url     : https://prove2.me/theorems/01005abe-2384-4fd5-9f15-cc7798d57a9a
-- title:
--   Paper: lg add four
-- statement:
--   For n ≥ 4: 2 ≤ log n ≤ log(n+4), 1 ≤ log log n, and 0 ≤ log log(n+4) ≤ 2·log log n.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/variables/VariableBound/Paper/Arith.lean#L79-L103
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/variables/VariableBound/Paper/Arith.lean#L79-L103

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

theorem VariableBound.Paper.lg_add_four {n : ℕ} (hn : 4 ≤ n) :
    2 ≤ lg n ∧ lg n ≤ lg ((n : ℝ) + 4) ∧ 1 ≤ lg (lg n) ∧ 0 ≤ lg (lg ((n : ℝ) + 4)) ∧ lg (lg ((n : ℝ) + 4)) ≤ 2 * lg (lg n) := by sorry
