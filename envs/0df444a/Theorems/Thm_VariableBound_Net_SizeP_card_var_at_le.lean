-- Prove2me | Theorems.Thm_VariableBound_Net_SizeP_card_var_at_le
-- name    : VariableBound.Net.SizeP.card_var_at_le
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-05T03:47:32.738181+00:00
-- url     : https://prove2.me/theorems/c9b2cb7c-e337-4c09-87bf-71cfdc37ab90
-- title:
--   Size P: card var at le
-- statement:
--   The objects whose clause has a variable at a: at most Δ⌈n/g⌉·(1 + c), if 0 < g, the data are
--   well-formed (`WfD`), every variable occurs in at most Δ clauses and load(E) ≤ c for every clause.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/variables/VariableBound/Net/SizeP.lean#L116-L131
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/variables/VariableBound/Net/SizeP.lean#L116-L131

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

theorem VariableBound.Net.SizeP.card_var_at_le (hg : 0 < g) (hW : WfD k n D) (hΔ : ∀ v, (occ D.1 v).length ≤ Δ) {c : ℕ} (hc : ∀ e < D.1.length, colD D e ≤ c) (a : ℕ) :
    #((range (objs D).length).filter fun o => ∃ l ∈ clOf D o, l.1 / qv g n = a) ≤ qv g n * Δ * (1 + c) := by sorry
