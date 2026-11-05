-- Prove2me | Theorems.Thm_VariableBound_Net_Tuples_sl_subset_Vof
-- name    : VariableBound.Net.Tuples.sl_subset_Vof
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-05T03:46:30.37176+00:00
-- url     : https://prove2.me/theorems/b80f71b4-c46b-4990-a479-6265bf90d274
-- title:
--   Tuples: sl subset Vof
-- statement:
--   If ξ violates the clauses of all members of P, then ξ violates the clauses of every part of P.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/variables/VariableBound/Net/Tuples.lean#L215-L220
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/variables/VariableBound/Net/Tuples.lean#L215-L220

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

theorem VariableBound.Net.Tuples.sl_subset_Vof {σ : Fin n → Bool} {P : Finset ℕ} (hP : P ⊆ vset (Mark.ext σ) D) (κ j : ℕ) : sl D κ j P ⊆ Vof D.1 σ := by sorry
