-- Prove2me | Theorems.Thm_VariableBound_Net_SizeP_sum_capD_le
-- name    : VariableBound.Net.SizeP.sum_capD_le
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-05T03:47:21.255853+00:00
-- url     : https://prove2.me/theorems/569604be-c2fa-4a75-a0b3-a5de65333e15
-- title:
--   Size P: sum cap D le
-- statement:
--   The capacities at a node a < g sum to at most twice the number of objects that touch a: «an
--   object has at most two tests at a, and ⌈log C(t, μ)⌉ ≤ t».
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/variables/VariableBound/Net/SizeP.lean#L203-L206
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/variables/VariableBound/Net/SizeP.lean#L203-L206

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_VariableBound_Net_Tests
import Definitions.Def_VariableBound_Net_SizeB
import Definitions.Def_PaddedDescent_F_MarkDeg
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Algebra.Order.Floor.Semiring
import Mathlib.Data.Nat.Choose.Bounds
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Definitions.Def_VariableBound_Net_SizeP
import Theorems.Thm_Groundwork_PolyT_length
attribute [local fun_prop] Groundwork.PolyT.length


set_option autoImplicit false
section
section
open VariableBound VariableBound.Net VariableBound.Net.SizeP
open Groundwork Groundwork.Prog Finset
open PaddedDescent.F.Mark (Cl qv WfL occ)
variable {k g n Δ : ℕ} {D : Dat}

theorem VariableBound.Net.SizeP.sum_capD_le (y : ℕ) {a : ℕ} (ha : a < g) : ∑ b ∈ (range g).erase a, capD g n D y a b ≤ 2 * (tch g n D a).length := by sorry
