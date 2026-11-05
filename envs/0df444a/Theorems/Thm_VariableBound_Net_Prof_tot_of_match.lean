-- Prove2me | Theorems.Thm_VariableBound_Net_Prof_tot_of_match
-- name    : VariableBound.Net.Prof.tot_of_match
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-05T02:00:15.349308+00:00
-- url     : https://prove2.me/theorems/fd7d13bd-6593-4098-8bd2-a90c14ddcea3
-- title:
--   Prof: tot of match
-- statement:
--   Step 3, «Profiles»: the profile y of a term has Σ_a μ_(a,κ) equal to the number of members of P
--   of kind κ, that is |Π₀| for κ = 0 and the number of marked incidences for κ = 1. Needs 0 < g,
--   well-formed data, that P is a set of positions of objects,
--   κ < 2, and that P belongs to y.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/variables/VariableBound/Net/Prof.lean#L255-L258
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/variables/VariableBound/Net/Prof.lean#L255-L258

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
attribute [local fun_prop] Groundwork.PolyT.length


set_option autoImplicit false
section
section
open VariableBound VariableBound.Net VariableBound.Net.Prof
open Groundwork Groundwork.Prog Groundwork.Grid PaddedDescent.F Finset
open PaddedDescent.F.Mark (Cl qv vio WfL occ nProf)

theorem VariableBound.Net.Prof.tot_of_match {k g n : ℕ} {D : Dat} (hg : 0 < g) (h : WfD k n D) {P : Finset ℕ} (hP : P ⊆ range (objs D).length) {y : ℕ}
    (hM : Match g n D y P) {κ : ℕ} (hκ : κ < 2) : tot g D y κ = (kP D P κ).card := by sorry
