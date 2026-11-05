-- Prove2me | Theorems.Thm_PaddedDescent_F_Mark_Pi_countP_cls
-- name    : PaddedDescent.F.Mark.Pi.countP_cls
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T02:43:13.704199+00:00
-- url     : https://prove2.me/theorems/dcabf118-2657-4056-b21f-3ab3d0ea908b
-- title:
--   Pi: count P cls
-- statement:
--   Among all clauses, those of layer i with the property p are as many as the clauses with p in the
--   list of layer i.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/PaddedDescent/F/MarkPi.lean#L233-L250
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/PaddedDescent/F/MarkPi.lean#L233-L250

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_PaddedDescent_F_Interfaces
import Mathlib.Algebra.BigOperators.Intervals
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Data.Finset.Powerset
import Mathlib.Data.Nat.Choose.Sum
import Definitions.Def_PaddedDescent_F_MarkPi
import Theorems.Thm_Groundwork_PolyT_countP
attribute [local fun_prop] Groundwork.PolyT.countP


set_option autoImplicit false
section
open PaddedDescent PaddedDescent.F PaddedDescent.F.Mark PaddedDescent.F.Mark.Pi
open Finset Groundwork Groundwork.Prog
variable {ι : Type*} [DecidableEq ι]

theorem PaddedDescent.F.Mark.Pi.countP_cls (p : Cl → Bool) (Ls : List Fml) (i : ℕ) :
    (cls Ls).countP (fun q => p q.2 && decide (q.1 = i)) = (Ls.getD i []).countP p := by sorry
