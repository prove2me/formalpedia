-- Prove2me | Theorems.Thm_VariableBound_Net_SizeP_sized_PD
-- name    : VariableBound.Net.SizeP.sized_PD
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T03:48:02.265213+00:00
-- url     : https://prove2.me/theorems/67d7eea5-4810-4cc6-bc75-defa19266833
-- title:
--   Size P: sized PD
-- statement:
--   Step 3, «The parameters»: the network of a profile has size P = ⌈2P₀⌉ with values bounded by
--   2^B, if |W_a| ≤ 2^B at every node a < g, and 0 < g, 0 ≤ s̄, the data are well-formed (`WfD`), every
--   variable
--   occurs in at most Δ clauses, r ≤ r̄, |Λ_j| ≤ s̄ for all j and load(E) ≤ t̄ + 2 for every clause.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/variables/VariableBound/Net/SizeP.lean#L301-L311
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/variables/VariableBound/Net/SizeP.lean#L301-L311

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

theorem VariableBound.Net.SizeP.sized_PD (hg : 0 < g) {tb rb B y : ℕ} {sb : ℚ} {fl : Bool} (hsb : 0 ≤ sb) (hW : WfD k n D) (hΔ : ∀ v, (occ D.1 v).length ≤ Δ) (hr : D.2.length ≤ rb)
    (hs : ∀ L ∈ D.2, (L.length : ℚ) ≤ sb) (hc : ∀ e < D.1.length, colD D e ≤ tb + 2) (h3 : ∀ a < g, ∀ z, |WD g n D y fl a z| ≤ 2 ^ B) :
    (netDN g (ctx g n D y fl)).Sized (PD g n Δ tb rb sb) B := by sorry
