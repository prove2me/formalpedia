-- Prove2me | Theorems.Thm_WidthK_Thresholds_sq_mul_theta_le
-- name    : WidthK.Thresholds.sq_mul_theta_le
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-04T19:43:46.730322+00:00
-- url     : https://prove2.me/theorems/cc76cec9-1684-4cd9-94f9-62408f06c1c4
-- title:
--   Thresholds: sq mul theta le
-- statement:
--   τ² · θ i ≤ τ^(2^(i+1)) for τ ≥ 4: by the previous lemma the quantity τ² · θ i is at most squared
--   in each step.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/sparsification/SparsifyWidthK/Thresholds.lean#L114-L125
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/sparsification/SparsifyWidthK/Thresholds.lean#L114-L125

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

theorem WidthK.Thresholds.sq_mul_theta_le {τ : ℕ} (hτ : 4 ≤ τ) (i : ℕ) : τ ^ 2 * theta τ i ≤ τ ^ 2 ^ (i + 1) := by sorry
