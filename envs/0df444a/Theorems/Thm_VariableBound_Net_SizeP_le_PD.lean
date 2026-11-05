-- Prove2me | Theorems.Thm_VariableBound_Net_SizeP_le_PD
-- name    : VariableBound.Net.SizeP.le_PD
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-05T03:48:05.057794+00:00
-- url     : https://prove2.me/theorems/0cd39cb8-aa38-4414-9ded-358bf24d893a
-- title:
--   Size P: le PD
-- statement:
--   A natural number that is at most 2P₀ is at most P = ⌈2P₀⌉.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/variables/VariableBound/Net/SizeP.lean#L293-L295
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/variables/VariableBound/Net/SizeP.lean#L293-L295

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
set_option autoImplicit false
section
section
open VariableBound VariableBound.Net VariableBound.Net.SizeP
open Groundwork Groundwork.Prog Finset
open PaddedDescent.F.Mark (Cl qv WfL occ)
variable {k g n Δ : ℕ} {D : Dat}

theorem VariableBound.Net.SizeP.le_PD {tb rb x : ℕ} {sb : ℚ} (h : (x : ℚ) ≤ 2 * P0 g n Δ tb rb sb) : x ≤ PD g n Δ tb rb sb := by sorry
