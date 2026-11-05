-- Prove2me | Theorems.Thm_VariableBound_Net_Tuples_mem_back
-- name    : VariableBound.Net.Tuples.mem_back
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T00:19:33.41013+00:00
-- url     : https://prove2.me/theorems/71b13088-09d0-4c5f-a31c-2bc7152dcac4
-- title:
--   Tuples: mem back
-- statement:
--   The members of the set put together from (S₀, S) are the objects E with E ∈ S₀ and (E, j) with E
--   ∈ S j.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/variables/VariableBound/Net/Tuples.lean#L93-L95
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/variables/VariableBound/Net/Tuples.lean#L93-L95

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

theorem VariableBound.Net.Tuples.mem_back {r : ℕ} {S₀ : Finset (Fin D.1.length)} {S : Fin r → Finset (Fin D.1.length)} {o : ℕ} :
    o ∈ back D S₀ S ↔ o < (objs D).length ∧ ((∃ e ∈ S₀, obAt D o = (0, e.val, 0)) ∨ ∃ j, ∃ e ∈ S j, obAt D o = (1, e.val, j.val)) := by sorry
