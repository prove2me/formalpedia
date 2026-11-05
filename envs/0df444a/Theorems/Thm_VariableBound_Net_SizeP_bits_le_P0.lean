-- Prove2me | Theorems.Thm_VariableBound_Net_SizeP_bits_le_P0
-- name    : VariableBound.Net.SizeP.bits_le_P0
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-05T03:47:58.332048+00:00
-- url     : https://prove2.me/theorems/9026b7d6-cb09-4648-8275-6b891a1dd1ca
-- title:
--   Size P: bits le P0
-- statement:
--   Step 3, «The parameters»: «so z_a has at most P₀ bits», if 0 < g, 0 ≤ s̄, the data are
--   well-formed (`WfD`), every variable occurs in at most Δ clauses, r ≤ r̄, |Λ_j| ≤ s̄ for all j and
--   load(E) ≤ t̄ + 2 for
--   every clause.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/variables/VariableBound/Net/SizeP.lean#L280-L290
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/variables/VariableBound/Net/SizeP.lean#L280-L290

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

theorem VariableBound.Net.SizeP.bits_le_P0 (hg : 0 < g) {tb rb : ℕ} {sb : ℚ} (hsb : 0 ≤ sb) (hW : WfD k n D) (hΔ : ∀ v, (occ D.1 v).length ≤ Δ) (hr : D.2.length ≤ rb)
    (hs : ∀ L ∈ D.2, (L.length : ℚ) ≤ sb) (hc : ∀ e < D.1.length, colD D e ≤ tb + 2) (a : ℕ) :
    ((qv g n + (tch g n D a).length : ℕ) : ℚ) ≤ P0 g n Δ tb rb sb := by sorry
