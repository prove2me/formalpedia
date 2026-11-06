-- Prove2me | Theorems.Thm_VariableBound_Net_SizeB_card_marked_le
-- name    : VariableBound.Net.SizeB.card_marked_le
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T03:47:15.240738+00:00
-- url     : https://prove2.me/theorems/1ff455c0-f3c9-420c-b2fe-6264c2b1421f
-- title:
--   Size B: card marked le
-- statement:
--   Step 3, «The parameters»: a setting z of the node a < g in the network of the profile y has at
--   most μ_(a,1) + Σ_(b ≠ a) μ_(a,b,1) marked incidences.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/variables/VariableBound/Net/SizeB.lean#L140-L162
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/variables/VariableBound/Net/SizeB.lean#L140-L162

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
set_option autoImplicit false
section
open VariableBound VariableBound.Net VariableBound.Net.SizeB
open Groundwork Groundwork.Prog Finset PaddedDescent.F VariableBound.Net.Basic
open PaddedDescent.F.Mark (Cl qv vio WfL occ)
variable {k g n : ℕ} {D : Dat} {y : ℕ}

theorem VariableBound.Net.SizeB.card_marked_le {a : ℕ} {z : List Bool} (ha : a < g) (h : okD g n D y a z = true) :
    #(mk g n D a z) ≤ mu g D y a a 1 + ∑ b ∈ (range g).erase a, mu g D y a b 1 := by sorry
