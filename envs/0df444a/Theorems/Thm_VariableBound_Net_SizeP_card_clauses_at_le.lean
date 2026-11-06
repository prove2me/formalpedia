-- Prove2me | Theorems.Thm_VariableBound_Net_SizeP_card_clauses_at_le
-- name    : VariableBound.Net.SizeP.card_clauses_at_le
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T03:47:03.876441+00:00
-- url     : https://prove2.me/theorems/9ea2ea9d-aa4a-4bc0-8163-8c55742865f2
-- title:
--   Size P: card clauses at le
-- statement:
--   Step 3, «The parameters»: «at most Δ⌈n/g⌉ clauses have a variable at a», if 0 < g, the data are
--   well-formed (`WfD`) and every variable occurs in at most Δ clauses.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/variables/VariableBound/Net/SizeP.lean#L62-L83
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/variables/VariableBound/Net/SizeP.lean#L62-L83

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

theorem VariableBound.Net.SizeP.card_clauses_at_le (hg : 0 < g) (hW : WfD k n D) (hΔ : ∀ v, (occ D.1 v).length ≤ Δ) (a : ℕ) :
    #((range D.1.length).filter fun e => ∃ l ∈ D.1.getD e [], l.1 / qv g n = a) ≤ qv g n * Δ := by sorry
