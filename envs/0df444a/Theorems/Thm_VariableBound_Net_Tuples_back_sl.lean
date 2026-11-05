-- Prove2me | Theorems.Thm_VariableBound_Net_Tuples_back_sl
-- name    : VariableBound.Net.Tuples.back_sl
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T03:46:28.549211+00:00
-- url     : https://prove2.me/theorems/0a4a9657-26be-4a72-8b2b-5a65f9197f8d
-- title:
--   Tuples: back sl
-- statement:
--   Cutting and putting together again gives back a set P of positions of objects, for well-formed
--   data.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/variables/VariableBound/Net/Tuples.lean#L146-L163
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/variables/VariableBound/Net/Tuples.lean#L146-L163

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

theorem VariableBound.Net.Tuples.back_sl (hW : WfD k n D) {P : Finset ℕ} (hP : P ⊆ range (objs D).length) :
    back D (sl D 0 0 P) (fun j : Fin (chks D).length => sl D 1 j.val P) = P := by sorry
