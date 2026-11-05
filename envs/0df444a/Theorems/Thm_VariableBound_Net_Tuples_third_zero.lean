-- Prove2me | Theorems.Thm_VariableBound_Net_Tuples_third_zero
-- name    : VariableBound.Net.Tuples.third_zero
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T02:00:42.078102+00:00
-- url     : https://prove2.me/theorems/e9c3f8c1-74cd-4f67-a945-bb0e9b4dd5bd
-- title:
--   Tuples: third zero
-- statement:
--   An object of kind 0 is a triple (0, e, 0): the third entry of an object o (a place below the
--   number of objects) of kind 0 is 0.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/variables/VariableBound/Net/Tuples.lean#L99-L102
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/variables/VariableBound/Net/Tuples.lean#L99-L102

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

theorem VariableBound.Net.Tuples.third_zero {o : ℕ} (h : o < (objs D).length) (h0 : (obAt D o).1 = 0) : (obAt D o).2.2 = 0 := by sorry
