-- Prove2me | Theorems.Thm_VariableBound_Net_SizeP_length_tch_le
-- name    : VariableBound.Net.SizeP.length_tch_le
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T02:01:30.444507+00:00
-- url     : https://prove2.me/theorems/c612f46f-b67e-496d-a1b8-465826939051
-- title:
--   Size P: length tch le
-- statement:
--   The number of objects that touch a: at most Δ⌈n/g⌉·(1 + c) plus the sizes of the checks with
--   home a, if 0 < g, the data are well-formed (`WfD`), every variable occurs in at most Δ clauses and
--   load(E) ≤ c for every clause.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/variables/VariableBound/Net/SizeP.lean#L159-L170
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/variables/VariableBound/Net/SizeP.lean#L159-L170

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
import Theorems.Thm_PaddedDescent_F_Mark_Deg_length_tch_le
attribute [local fun_prop] Groundwork.PolyT.filter
attribute [local fun_prop] Groundwork.PolyT.length


set_option autoImplicit false
section
section
open VariableBound VariableBound.Net VariableBound.Net.SizeP
open Groundwork Groundwork.Prog Finset
open PaddedDescent.F.Mark (Cl qv WfL occ)
variable {k g n Δ : ℕ} {D : Dat}

theorem VariableBound.Net.SizeP.length_tch_le (hg : 0 < g) (hW : WfD k n D) (hΔ : ∀ v, (occ D.1 v).length ≤ Δ) {c : ℕ} (hc : ∀ e < D.1.length, colD D e ≤ c) (a : ℕ) :
    (tch g n D a).length ≤ qv g n * Δ * (1 + c) + ∑ j ∈ (range D.2.length).filter (fun j => home g j = a), (D.2.getD j []).length := by sorry
