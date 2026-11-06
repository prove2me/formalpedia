-- Prove2me | Theorems.Thm_VariableBound_Net_Prof_sum_oc
-- name    : VariableBound.Net.Prof.sum_oc
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T03:45:33.979061+00:00
-- url     : https://prove2.me/theorems/7cc07d6d-3890-46e5-94f7-6f9347823174
-- title:
--   Prof: sum oc
-- statement:
--   Step 3, «Profiles»: Σ_a μ_(a,κ) is the number of marked objects of kind κ, that is |Π₀| for κ =
--   0 and the number of marked incidences for κ = 1. Here for the numbers of P: the members of kind κ
--   that the nodes
--   own add up to the members of kind κ. Needs 0 < g, well-formed data, and that P is a set of positions
--   of objects.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/variables/VariableBound/Net/Prof.lean#L188-L201
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/variables/VariableBound/Net/Prof.lean#L188-L201

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_VariableBound_Net_Basic
import Definitions.Def_StepMachines_Math_Digits
import Definitions.Def_PaddedDescent_F_MarkProf
import Mathlib.Data.Finset.Max
import Mathlib.Data.Finset.Prod
import Mathlib.Algebra.BigOperators.Group.Finset.Sigma
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Algebra.Order.BigOperators.Group.List
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Tauto
import Definitions.Def_VariableBound_Net_Prof
import Theorems.Thm_Groundwork_PolyT_length
import Theorems.Thm_PaddedDescent_F_Mark_Prof_sum_oc
attribute [local fun_prop] Groundwork.PolyT.length


set_option autoImplicit false
section
section
open VariableBound VariableBound.Net VariableBound.Net.Prof
open Groundwork Groundwork.Prog Groundwork.Grid PaddedDescent.F Finset
open PaddedDescent.F.Mark (Cl qv vio WfL occ nProf)

theorem VariableBound.Net.Prof.sum_oc {k g n : ℕ} {D : Dat} (hg : 0 < g) (h : WfD k n D) {P : Finset ℕ} (hP : P ⊆ range (objs D).length) (κ : ℕ) :
    ∑ a ∈ range g, oc g n D P a κ = (kP D P κ).card := by sorry
