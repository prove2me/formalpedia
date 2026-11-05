-- Prove2me | Theorems.Thm_WidthK_Thresholds_bsum_le_pow
-- name    : WidthK.Thresholds.bsum_le_pow
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-04T19:44:13.137957+00:00
-- url     : https://prove2.me/theorems/017445cb-e385-4969-9404-a0c9d496bfa7
-- title:
--   Thresholds: bsum le pow
-- statement:
--   2 + β 1 + … + β i ≤ τ^(2^(i+1)) for τ ≥ 4.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/sparsification/SparsifyWidthK/Thresholds.lean#L128-L130
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/sparsification/SparsifyWidthK/Thresholds.lean#L128-L130

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

theorem WidthK.Thresholds.bsum_le_pow {τ : ℕ} (hτ : 4 ≤ τ) (i : ℕ) : bsum τ i ≤ τ ^ 2 ^ (i + 1) := by sorry
