-- Prove2me | Theorems.Thm_VariableBound_Net_SizeB_stP
-- name    : VariableBound.Net.SizeB.stP
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T03:47:51.760286+00:00
-- url     : https://prove2.me/theorems/4060d7c0-5f7a-47e5-90b5-b3743d34e74a
-- title:
--   Size B: st P
-- statement:
--   Display (69): gP ≤ 2(n + g)(1 + Δ(t̄ + 3)) + 2(10n + g)·s̄ + g, for g > 0, s̄ ≥ 0 and r̄ ≤ 10n,
--   with P = ⌈2P₀⌉ and P₀ = ⌈n/g⌉(1 + Δ(t̄ + 3)) + ⌈r̄/g⌉·s̄.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/variables/VariableBound/Net/SizeB.lean#L267-L285
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/variables/VariableBound/Net/SizeB.lean#L267-L285

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_VariableBound_Net_Defs
import Definitions.Def_VariableBound_Net_Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Sigma
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Algebra.Order.Floor.Semiring
import Mathlib.Algebra.Order.Ring.Abs
import Mathlib.Data.List.Nodup
import Mathlib.Data.Rat.Floor
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring
import Definitions.Def_VariableBound_Net_SizeB
set_option autoImplicit false
section
open VariableBound VariableBound.Net VariableBound.Net.SizeB
open Groundwork Groundwork.Prog Finset PaddedDescent.F VariableBound.Net.Basic
open PaddedDescent.F.Mark (Cl qv vio WfL occ)
variable {k g n : ℕ} {D : Dat} {y : ℕ}

theorem VariableBound.Net.SizeB.stP : StP := by sorry
