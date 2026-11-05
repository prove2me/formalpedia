-- Prove2me | Theorems.Thm_PaddedDescent_F_Mark_Pi_layer_lt
-- name    : PaddedDescent.F.Mark.Pi.layer_lt
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T00:24:44.986389+00:00
-- url     : https://prove2.me/theorems/5de88607-b6ad-44bd-9649-1c02d743ab89
-- title:
--   Pi: layer lt
-- statement:
--   The layer of a clause of the list of all clauses is below the number of layers.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/PaddedDescent/F/MarkPi.lean#L222-L229
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/PaddedDescent/F/MarkPi.lean#L222-L229

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_PaddedDescent_F_Interfaces
import Mathlib.Algebra.BigOperators.Intervals
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Data.Finset.Powerset
import Mathlib.Data.Nat.Choose.Sum
import Definitions.Def_PaddedDescent_F_MarkPi
import Theorems.Thm_Groundwork_PolyT_length
attribute [local fun_prop] Groundwork.PolyT.length


set_option autoImplicit false
section
open PaddedDescent PaddedDescent.F PaddedDescent.F.Mark PaddedDescent.F.Mark.Pi
open Finset Groundwork Groundwork.Prog
variable {ι : Type*} [DecidableEq ι]

theorem PaddedDescent.F.Mark.Pi.layer_lt (Ls : List Fml) {e : ℕ} (he : e < (cls Ls).length) : (clAt Ls e).1 < Ls.length := by sorry
