-- Prove2me | Theorems.Thm_VariableBound_Search_argminD_eq
-- name    : VariableBound.Search.argminD_eq
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-04T20:09:34.078425+00:00
-- url     : https://prove2.me/theorems/093adf1a-08a4-47a5-958e-0a76d78a699f
-- title:
--   Search: argmin D eq
-- statement:
--   `argminD` is the fold of `stepD`.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/variables/VariableBound/Search/Correct.lean#L112-L116
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/variables/VariableBound/Search/Correct.lean#L112-L116

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_VariableBound_Search_Defs
import Definitions.Def_VariableBound_StepChoice
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Algebra.Order.Field.Basic
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring
import Definitions.Def_VariableBound_Search_Correct
import Theorems.Thm_Groundwork_PolyT_elim

set_option autoImplicit false
section
section
open VariableBound VariableBound.Search
open Groundwork PaddedDescent.F AppVariables Finset

theorem VariableBound.Search.argminD_eq (key : List ℕ → ℤ) (fam : List (List ℕ)) : argminD key fam = (fam.foldl (stepD key) none).elim [] fun b => b.1 := by sorry
