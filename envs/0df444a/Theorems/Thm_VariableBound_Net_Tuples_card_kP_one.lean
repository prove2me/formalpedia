-- Prove2me | Theorems.Thm_VariableBound_Net_Tuples_card_kP_one
-- name    : VariableBound.Net.Tuples.card_kP_one
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T03:46:21.719301+00:00
-- url     : https://prove2.me/theorems/07acf3a8-8ed4-4872-a744-4c7ee2c0841e
-- title:
--   Tuples: card k P one
-- statement:
--   |Π₁| + … + |Π_r| is the number of members of P of kind 1, for well-formed data (WfD) and a set P
--   of places of objects.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/variables/VariableBound/Net/Tuples.lean#L135-L142
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/variables/VariableBound/Net/Tuples.lean#L135-L142

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

theorem VariableBound.Net.Tuples.card_kP_one (hW : WfD k n D) {P : Finset ℕ} (hP : P ⊆ range (objs D).length) : #(kP D P 1) = ∑ j : Fin (chks D).length, #(sl D 1 j.val P) := by sorry
