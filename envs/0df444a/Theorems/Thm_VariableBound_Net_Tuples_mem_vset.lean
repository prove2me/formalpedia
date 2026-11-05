-- Prove2me | Theorems.Thm_VariableBound_Net_Tuples_mem_vset
-- name    : VariableBound.Net.Tuples.mem_vset
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T02:02:46.763944+00:00
-- url     : https://prove2.me/theorems/b209693a-3ed4-4d42-a982-970ee865eab1
-- title:
--   Tuples: mem vset
-- statement:
--   An object is in `vset` iff the assignment violates its clause.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/variables/VariableBound/Net/Tuples.lean#L211-L212
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/variables/VariableBound/Net/Tuples.lean#L211-L212

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

theorem VariableBound.Net.Tuples.mem_vset {σ : ℕ → Bool} {o : ℕ} : o ∈ vset σ D ↔ o < (objs D).length ∧ vio σ (D.1.getD (obAt D o).2.1 []) = true := by sorry
