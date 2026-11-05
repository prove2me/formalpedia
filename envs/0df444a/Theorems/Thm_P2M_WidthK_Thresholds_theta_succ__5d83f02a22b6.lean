-- Prove2me | Theorems.Thm_P2M_WidthK_Thresholds_theta_succ__5d83f02a22b6
-- name    : P2M_WidthK_Thresholds_theta_succ__5d83f02a22b6
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-04T19:38:53.448924+00:00
-- url     : https://prove2.me/theorems/74b30fb3-92c9-4ad4-8fe0-c90cb0fd9982
-- title:
--   P2 M Width K Thresholds theta succ  5d83f02a22b6: P2 M Width K Thresholds theta succ  5d83f02a22b6
-- statement:
--   The recursion for θ as it is written in the definition.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/sparsification/SparsifyWidthK/Thresholds.lean#L47-L47
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/sparsification/SparsifyWidthK/Thresholds.lean#L47-L47

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

theorem P2M_WidthK_Thresholds_theta_succ__5d83f02a22b6 (τ i : ℕ) : theta τ (i + 1) = 2 * τ * theta τ i * bsum τ i := by sorry

alias «WidthK».«Thresholds».«theta_succ'» := P2M_WidthK_Thresholds_theta_succ__5d83f02a22b6
