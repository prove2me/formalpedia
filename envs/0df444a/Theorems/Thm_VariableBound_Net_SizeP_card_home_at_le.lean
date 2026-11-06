-- Prove2me | Theorems.Thm_VariableBound_Net_SizeP_card_home_at_le
-- name    : VariableBound.Net.SizeP.card_home_at_le
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T03:46:37.367815+00:00
-- url     : https://prove2.me/theorems/f705068a-21a1-48c6-b241-ad631dbaca93
-- title:
--   Size P: card home at le
-- statement:
--   The incidences of the checks with home a: at most the sum of the sizes of these checks (for
--   well-formed data, `WfD`).
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/variables/VariableBound/Net/SizeP.lean#L135-L154
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/variables/VariableBound/Net/SizeP.lean#L135-L154

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
import Theorems.Thm_Groundwork_PolyT_filter
import Theorems.Thm_Groundwork_PolyT_length
attribute [local fun_prop] Groundwork.PolyT.filter
attribute [local fun_prop] Groundwork.PolyT.length


set_option autoImplicit false
section
section
open VariableBound VariableBound.Net VariableBound.Net.SizeP
open Groundwork Groundwork.Prog Finset
open PaddedDescent.F.Mark (Cl qv WfL occ)
variable {k g n Δ : ℕ} {D : Dat}

theorem VariableBound.Net.SizeP.card_home_at_le (hW : WfD k n D) (a : ℕ) :
    #((range (objs D).length).filter fun o => (obAt D o).1 = 1 ∧ home g (obAt D o).2.2 = a) ≤
      ∑ j ∈ (range D.2.length).filter (fun j => home g j = a), (D.2.getD j []).length := by sorry
