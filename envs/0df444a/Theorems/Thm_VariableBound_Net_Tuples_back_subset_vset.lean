-- Prove2me | Theorems.Thm_VariableBound_Net_Tuples_back_subset_vset
-- name    : VariableBound.Net.Tuples.back_subset_vset
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-05T03:45:02.651084+00:00
-- url     : https://prove2.me/theorems/7073f66c-c3cc-484c-9a5a-411cbcf3db40
-- title:
--   Tuples: back subset vset
-- statement:
--   If ξ violates all clauses of S₀ and of the S j, then ξ violates the clauses of all members of
--   the set put together.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/variables/VariableBound/Net/Tuples.lean#L233-L238
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/variables/VariableBound/Net/Tuples.lean#L233-L238

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

theorem VariableBound.Net.Tuples.back_subset_vset {σ : Fin n → Bool} {r : ℕ} {S₀ : Finset (Fin D.1.length)} {S : Fin r → Finset (Fin D.1.length)}
    (h0 : S₀ ⊆ Vof D.1 σ) (h1 : ∀ j, S j ⊆ Vof D.1 σ) : back D S₀ S ⊆ vset (Mark.ext σ) D := by sorry
