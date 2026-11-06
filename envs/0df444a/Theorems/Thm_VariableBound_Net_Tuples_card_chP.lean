-- Prove2me | Theorems.Thm_VariableBound_Net_Tuples_card_chP
-- name    : VariableBound.Net.Tuples.card_chP
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T03:45:59.988198+00:00
-- url     : https://prove2.me/theorems/dde97b29-d4bd-4923-afd8-82f28aad7491
-- title:
--   Tuples: card ch P
-- statement:
--   |Π_j| is the number of members of P that are incidences of check j, for well-formed data (WfD)
--   and a set P of places of objects.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/variables/VariableBound/Net/Tuples.lean#L130-L131
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/variables/VariableBound/Net/Tuples.lean#L130-L131

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

theorem VariableBound.Net.Tuples.card_chP (hW : WfD k n D) {P : Finset ℕ} (hP : P ⊆ range (objs D).length) (j : ℕ) : #(chP D P j) = #(sl D 1 j P) := by sorry
