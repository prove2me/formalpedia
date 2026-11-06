-- Prove2me | Theorems.Thm_VariableBound_Net_SizeB_okD_spec
-- name    : VariableBound.Net.SizeB.okD_spec
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T03:47:41.863866+00:00
-- url     : https://prove2.me/theorems/8ca6a4ae-27fd-4126-b9d3-256d7f5c3937
-- title:
--   Size B: ok D spec
-- statement:
--   What a setting of the profile y has: μ_(a,κ) marked objects of kind κ owned by a, and μ_(a,b,κ)
--   marked objects of kind κ with the test {a, b}.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/variables/VariableBound/Net/SizeB.lean#L131-L136
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/variables/VariableBound/Net/SizeB.lean#L131-L136

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
import Theorems.Thm_Groundwork_PolyT_count
import Theorems.Thm_Groundwork_PolyT_filter
import Theorems.Thm_Groundwork_PolyT_length
attribute [local fun_prop] Groundwork.PolyT.count
attribute [local fun_prop] Groundwork.PolyT.filter
attribute [local fun_prop] Groundwork.PolyT.length


set_option autoImplicit false
section
open VariableBound VariableBound.Net VariableBound.Net.SizeB
open Groundwork Groundwork.Prog Finset PaddedDescent.F VariableBound.Net.Basic
open PaddedDescent.F.Mark (Cl qv vio WfL occ)
variable {k g n : ℕ} {D : Dat} {y : ℕ}

theorem VariableBound.Net.SizeB.okD_spec {a : ℕ} {z : List Bool} (h : okD g n D y a z = true) :
    (∀ κ < 2, ((tch g n D a).filter fun o => (obAt D o).1 == κ && ownB g n D o a && mark g n D a z o).length = mu g D y a a κ) ∧
      ∀ b < g, b ≠ a → ∀ κ < 2, (str g n D a b κ z).count true = mu g D y a b κ := by sorry
