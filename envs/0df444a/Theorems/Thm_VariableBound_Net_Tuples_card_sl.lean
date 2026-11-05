-- Prove2me | Theorems.Thm_VariableBound_Net_Tuples_card_sl
-- name    : VariableBound.Net.Tuples.card_sl
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T00:54:14.188289+00:00
-- url     : https://prove2.me/theorems/ae15723e-88f8-4226-8acb-8020fa7e04d1
-- title:
--   Tuples: card sl
-- statement:
--   For well-formed data and a set P of positions of objects: there are as many clauses E with (κ,
--   E, j) in P as members of P of kind κ with third entry j.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/variables/VariableBound/Net/Tuples.lean#L106-L119
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/variables/VariableBound/Net/Tuples.lean#L106-L119

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_VariableBound_Net_Defs
import Definitions.Def_VariableBound_Net_Basic
import Mathlib.Tactic.Convert
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Data.Fintype.Pi
import Mathlib.Data.List.GetD
import Definitions.Def_VariableBound_Net_Tuples
import Theorems.Thm_Groundwork_PolyT_filter
import Theorems.Thm_Groundwork_PolyT_length
attribute [local fun_prop] Groundwork.PolyT.filter
attribute [local fun_prop] Groundwork.PolyT.length


set_option autoImplicit false
section
open VariableBound VariableBound.Net VariableBound.Net.Tuples
open Groundwork Groundwork.Prog Finset PaddedDescent.F VariableBound.Net.Basic
open PaddedDescent.F.Mark (Cl qv vio WfL occ)
open ClauseBound.ParityChecks (Vof)
variable {k n : ℕ} {D : Dat}

theorem VariableBound.Net.Tuples.card_sl (hW : WfD k n D) {P : Finset ℕ} (hP : P ⊆ range (objs D).length) (κ j : ℕ) :
    #(sl D κ j P) = #(P.filter fun o => (obAt D o).1 = κ ∧ (obAt D o).2.2 = j) := by sorry
