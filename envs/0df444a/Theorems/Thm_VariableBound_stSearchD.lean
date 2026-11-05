-- Prove2me | Theorems.Thm_VariableBound_stSearchD
-- name    : VariableBound.stSearchD
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-04T20:40:57.619279+00:00
-- url     : https://prove2.me/theorems/56de1b9e-3785-4cdf-95ad-e4beee1502eb
-- title:
--   Variable Bound: st Search D
-- statement:
--   Step 2, the algorithm as a program: under the hypotheses listed at `StSearchD`, the list that
--   `searchD` finds has the bounds of Step 2 (`StructD`) and X = 0.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/variables/VariableBound/Search/Correct.lean#L293-L302
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/variables/VariableBound/Search/Correct.lean#L293-L302

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
set_option autoImplicit false
section
section
open VariableBound
open Groundwork PaddedDescent.F AppVariables Finset

theorem VariableBound.stSearchD : StSearchD := by sorry
