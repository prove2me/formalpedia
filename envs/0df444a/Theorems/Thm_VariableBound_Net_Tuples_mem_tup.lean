-- Prove2me | Theorems.Thm_VariableBound_Net_Tuples_mem_tup
-- name    : VariableBound.Net.Tuples.mem_tup
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T03:46:04.64363+00:00
-- url     : https://prove2.me/theorems/4fc7a39a-f486-4784-85aa-86c4c57fa004
-- title:
--   Tuples: mem tup
-- statement:
--   S is a tuple (Π₁, …, Π_r) of the display after Lemma 12 (the right sides for X and F) iff Π_j ⊆
--   Λ_j ∩ V(ξ) for all j and |Π₁| + … + |Π_r| ≤ M.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/variables/VariableBound/Net/Tuples.lean#L202-L204
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/variables/VariableBound/Net/Tuples.lean#L202-L204

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

theorem VariableBound.Net.Tuples.mem_tup {X E : Type} [Fintype X] [Fintype E] [DecidableEq E] {V : X → Finset E} {L : List (Finset E)} {M : ℕ} {ξ : X} {S : Fin L.length → Finset E} :
    S ∈ AppVariables.tup V L M ξ ↔ (∀ j, S j ⊆ L.getD j.val ∅ ∩ V ξ) ∧ ∑ j, #(S j) ≤ M := by sorry
