-- Prove2me | Theorems.Thm_VariableBound_Count_not_vio_iff
-- name    : VariableBound.Count.not_vio_iff
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T03:49:49.481207+00:00
-- url     : https://prove2.me/theorems/28a06697-fe58-4ddd-919d-2e7f83b88fbb
-- title:
--   Count: not vio iff
-- statement:
--   A clause is not violated iff one of its literals is true.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/variables/VariableBound/Count/Correct.lean#L39-L42
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/variables/VariableBound/Count/Correct.lean#L39-L42

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_VariableBound_Count_Defs
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring
import Definitions.Def_VariableBound_Count_Correct
set_option autoImplicit false
section
section
open VariableBound VariableBound.Count
open Groundwork Groundwork.Prog PaddedDescent.F PaddedDescent.F.Mark ClauseBound.Alg ClauseBound.ParityChecks AppVariables VariableBound.Net Finset

theorem VariableBound.Count.not_vio_iff (σ : ℕ → Bool) (C : List (ℕ × Bool)) : ¬ vio σ C = true ↔ ∃ l ∈ C, σ l.1 = l.2 := by sorry
