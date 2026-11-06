-- Prove2me | Theorems.Thm_VariableBound_Net_SizeB_marked_le
-- name    : VariableBound.Net.SizeB.marked_le
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T03:47:11.242857+00:00
-- url     : https://prove2.me/theorems/35e727a3-ff83-42d4-b5f1-eebbc8a7f7f0
-- title:
--   Size B: marked le
-- statement:
--   Step 3, «The parameters»: «a setting of an admissible profile has at most (k + 1)M of them»
--   (marked incidences), for well-formed data, a node a < g and a setting z of the network of the
--   admissible profile y.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/variables/VariableBound/Net/SizeB.lean#L191-L212
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/variables/VariableBound/Net/SizeB.lean#L191-L212

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

theorem VariableBound.Net.SizeB.marked_le {nb M : ℕ} {fl : Bool} (hW : WfD k n D) (h : admD k g n nb M D fl y = true) {a : ℕ} (ha : a < g) {z : List Bool}
    (hz : okD g n D y a z = true) : #(mk g n D a z) ≤ (k + 1) * M := by sorry
