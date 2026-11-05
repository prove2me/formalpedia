-- Prove2me | Theorems.Thm_WidthK_Thresholds_two_le_bsum
-- name    : WidthK.Thresholds.two_le_bsum
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-04T19:37:36.680247+00:00
-- url     : https://prove2.me/theorems/ab3d9a78-a616-4f29-b3c3-07dcfcc78973
-- title:
--   Thresholds: two le bsum
-- statement:
--   The sum is at least 2.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/sparsification/SparsifyWidthK/Thresholds.lean#L75-L75
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/sparsification/SparsifyWidthK/Thresholds.lean#L75-L75

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

theorem WidthK.Thresholds.two_le_bsum (τ i : ℕ) : 2 ≤ bsum τ i := by sorry
