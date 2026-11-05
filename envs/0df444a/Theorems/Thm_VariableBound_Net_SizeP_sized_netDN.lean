-- Prove2me | Theorems.Thm_VariableBound_Net_SizeP_sized_netDN
-- name    : VariableBound.Net.SizeP.sized_netDN
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-05T02:03:41.887192+00:00
-- url     : https://prove2.me/theorems/bac61835-f4a5-43c2-84ac-76a8d37c41f7
-- title:
--   Size P: sized net DN
-- statement:
--   The network of the profile y has size P with values bounded by 2^B, if at every node a < g the
--   number ⌈n/g⌉ + (number of objects that touch a) of bits of a setting is at most P, twice the number
--   of
--   objects that touch a is at most P, and |W_a| ≤ 2^B.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/variables/VariableBound/Net/SizeP.lean#L219-L259
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/variables/VariableBound/Net/SizeP.lean#L219-L259

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

theorem VariableBound.Net.SizeP.sized_netDN {P B y : ℕ} {fl : Bool} (h1 : ∀ a < g, qv g n + (tch g n D a).length ≤ P) (h2 : ∀ a < g, 2 * (tch g n D a).length ≤ P)
    (h3 : ∀ a < g, ∀ z, |WD g n D y fl a z| ≤ 2 ^ B) : (netDN g (ctx g n D y fl)).Sized P B := by sorry
