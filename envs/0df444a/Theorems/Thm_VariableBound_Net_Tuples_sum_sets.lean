-- Prove2me | Theorems.Thm_VariableBound_Net_Tuples_sum_sets
-- name    : VariableBound.Net.Tuples.sum_sets
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T03:45:57.001338+00:00
-- url     : https://prove2.me/theorems/8dbfa170-6bfc-4cb3-a883-5025d841faaf
-- title:
--   Tuples: sum sets
-- statement:
--   Step 3, «the term is given by ξ and the sets Π₀ and Π_j»: for well-formed data and one ξ, the
--   sum of the terms of the sets P of objects with violated clauses, within the limits, is the sum over
--   the tuples
--   (Π₀, …, Π_r) of the display after Lemma 12.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/variables/VariableBound/Net/Tuples.lean#L258-L293
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/variables/VariableBound/Net/Tuples.lean#L258-L293

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
set_option autoImplicit false
section
open VariableBound VariableBound.Net VariableBound.Net.Tuples
open Groundwork Groundwork.Prog Finset PaddedDescent.F VariableBound.Net.Basic
open PaddedDescent.F.Mark (Cl qv vio WfL occ)
open ClauseBound.ParityChecks (Vof)
variable {k n : ℕ} {D : Dat}
open Classical

theorem VariableBound.Net.Tuples.sum_sets (hW : WfD k n D) (nb M : ℕ) (fl : Bool) (σ : Fin n → Bool) :
    (∑ P ∈ (vset (Mark.ext σ) D).powerset, if Lim nb M D fl P then wt D fl P else 0) =
      ∑ S₀ ∈ (Vof D.1 σ).powerset with (if fl = true then #S₀ ≤ nb else #S₀ = nb + 1),
        (bif fl then (-1) ^ #S₀ else 1) * ∑ S ∈ AppVariables.tup (Vof (n := n) D.1) (chks D) M σ, ∏ j, ParityChecks.sig #(S j) := by sorry
