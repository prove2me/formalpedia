-- Prove2me | Theorems.Thm_WidthK_Thresholds_add_two_le_bsum
-- name    : WidthK.Thresholds.add_two_le_bsum
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-04T20:21:00.066249+00:00
-- url     : https://prove2.me/theorems/4ceddf45-85f9-471e-8c52-65aa8a13c0ba
-- title:
--   Thresholds: add two le bsum
-- statement:
--   The sum grows by at least 1 with each step: i + 2 ≤ 2 + β 1 + … + β i.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/sparsification/SparsifyWidthK/Thresholds.lean#L87-L96
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/sparsification/SparsifyWidthK/Thresholds.lean#L87-L96

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_SparsifyWidthK_Interfaces
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Definitions.Def_StepMachines_Math_SparsifyCount
import Definitions.Def_StepMachines_Math_SparsifyCount
import Mathlib.Data.Nat.Choose.Sum
import Mathlib.Algebra.BigOperators.Intervals
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.FieldSimp
import Definitions.Def_SparsifyWidthK_Thresholds
import Theorems.Thm_Groundwork_PolyT_all
attribute [local fun_prop] Groundwork.PolyT.all


set_option autoImplicit false
section
section
open WidthK WidthK.Thresholds
open Finset

theorem WidthK.Thresholds.add_two_le_bsum {τ : ℕ} (hτ : 1 ≤ τ) (i : ℕ) : i + 2 ≤ bsum τ i := by sorry
