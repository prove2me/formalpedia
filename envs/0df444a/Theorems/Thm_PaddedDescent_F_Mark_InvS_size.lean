-- Prove2me | Theorems.Thm_PaddedDescent_F_Mark_InvS_size
-- name    : PaddedDescent.F.Mark.InvS.size
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-04T23:18:55.600744+00:00
-- url     : https://prove2.me/theorems/732d2663-95d4-40ed-834c-d41488d4cb47
-- title:
--   Inv S: size
-- statement:
--   From the inequality: the later layers hold at most about two thirds of the clauses.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/PaddedDescent/F/MarkLayers.lean#L277-L286
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/PaddedDescent/F/MarkLayers.lean#L277-L286

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_PaddedDescent_F_MarkSums
import Definitions.Def_PaddedDescent_F_Interfaces
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Tauto
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.GCongr
import Definitions.Def_PaddedDescent_F_MarkLayers
import Theorems.Thm_Groundwork_PolyT_length
attribute [local fun_prop] Groundwork.PolyT.length


set_option autoImplicit false
section
section
open PaddedDescent PaddedDescent.F PaddedDescent.F.Mark
open Finset Groundwork.Prog
open Layers

theorem PaddedDescent.F.Mark.InvS.size {n w : ℕ} {Λ : Fml} {rest : List Fml} (h : InvS n w Λ rest) :
    3 * rest.flatten.length ≤ 2 * (rest.flatten.length + Λ.length) + 5 := by sorry
