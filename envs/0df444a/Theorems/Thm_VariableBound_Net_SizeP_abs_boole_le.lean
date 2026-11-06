-- Prove2me | Theorems.Thm_VariableBound_Net_SizeP_abs_boole_le
-- name    : VariableBound.Net.SizeP.abs_boole_le
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T03:48:28.856008+00:00
-- url     : https://prove2.me/theorems/c46c8631-b459-4c65-aa2c-ff1a5b0ea762
-- title:
--   Size P: abs boole le
-- statement:
--   A number that is 0 or 1 is at most 1 in absolute value.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/variables/VariableBound/Net/SizeP.lean#L209-L210
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/variables/VariableBound/Net/SizeP.lean#L209-L210

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
import Theorems.Thm_Groundwork_Prog_Count_abs_boole_le

set_option autoImplicit false
section
section
open VariableBound VariableBound.Net VariableBound.Net.SizeP
open Groundwork Groundwork.Prog Finset
open PaddedDescent.F.Mark (Cl qv WfL occ)
variable {k g n Δ : ℕ} {D : Dat}

theorem VariableBound.Net.SizeP.abs_boole_le (p : Prop) [Decidable p] : |if p then (1 : ℤ) else 0| ≤ 1 := by sorry
