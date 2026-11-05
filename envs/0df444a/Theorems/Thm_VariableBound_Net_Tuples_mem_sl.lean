-- Prove2me | Theorems.Thm_VariableBound_Net_Tuples_mem_sl
-- name    : VariableBound.Net.Tuples.mem_sl
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-04T23:53:46.301693+00:00
-- url     : https://prove2.me/theorems/e441456d-b568-47c6-af6e-74aa400309d6
-- title:
--   Tuples: mem sl
-- statement:
--   E is in the part (κ, j) of P iff the object (κ, E, j) is a member of P.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/variables/VariableBound/Net/Tuples.lean#L88-L89
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/variables/VariableBound/Net/Tuples.lean#L88-L89

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
import Theorems.Thm_Groundwork_PolyT_length
attribute [local fun_prop] Groundwork.PolyT.length


set_option autoImplicit false
section
open VariableBound VariableBound.Net VariableBound.Net.Tuples
open Groundwork Groundwork.Prog Finset PaddedDescent.F VariableBound.Net.Basic
open PaddedDescent.F.Mark (Cl qv vio WfL occ)
open ClauseBound.ParityChecks (Vof)
variable {k n : ℕ} {D : Dat}

theorem VariableBound.Net.Tuples.mem_sl {κ j : ℕ} {P : Finset ℕ} {e : Fin D.1.length} : e ∈ sl D κ j P ↔ ∃ o ∈ P, obAt D o = (κ, e.val, j) := by sorry
