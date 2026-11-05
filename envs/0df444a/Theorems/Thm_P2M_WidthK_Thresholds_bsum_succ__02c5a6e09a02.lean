-- Prove2me | Theorems.Thm_P2M_WidthK_Thresholds_bsum_succ__02c5a6e09a02
-- name    : P2M_WidthK_Thresholds_bsum_succ__02c5a6e09a02
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-04T19:44:17.278318+00:00
-- url     : https://prove2.me/theorems/855c5af1-d054-4ecc-aee4-5babc89be6e1
-- title:
--   P2 M Width K Thresholds bsum succ  02c5a6e09a02: P2 M Width K Thresholds bsum succ  02c5a6e09a02
-- statement:
--   The recursion for the sum as it is written in the definition.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/sparsification/SparsifyWidthK/Thresholds.lean#L50-L50
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/sparsification/SparsifyWidthK/Thresholds.lean#L50-L50

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

theorem P2M_WidthK_Thresholds_bsum_succ__02c5a6e09a02 (τ i : ℕ) : bsum τ (i + 1) = bsum τ i * (1 + 2 * theta τ i) := by sorry

alias «WidthK».«Thresholds».«bsum_succ'» := P2M_WidthK_Thresholds_bsum_succ__02c5a6e09a02
