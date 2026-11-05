-- Prove2me | Theorems.Thm_WidthK_Thresholds_bsum_eq
-- name    : WidthK.Thresholds.bsum_eq
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-04T19:41:13.612543+00:00
-- url     : https://prove2.me/theorems/f53b4c6f-b7ee-423c-a5ed-c63422354574
-- title:
--   Thresholds: bsum eq
-- statement:
--   `bsum τ i` is indeed 2 + β 0 + β 1 + … + β i (and β 0 = 0).
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/sparsification/SparsifyWidthK/Thresholds.lean#L67-L70
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/sparsification/SparsifyWidthK/Thresholds.lean#L67-L70

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

theorem WidthK.Thresholds.bsum_eq (τ i : ℕ) : bsum τ i = 2 + ∑ j ∈ range (i + 1), beta τ j := by sorry
