-- Prove2me | Theorems.Thm_PaddedDescent_F_Mark_trunc_sub_trunc
-- name    : PaddedDescent.F.Mark.trunc_sub_trunc
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T03:30:00.680233+00:00
-- url     : https://prove2.me/theorems/e331c634-b6f0-4e97-8d03-37a911dd4558
-- title:
--   Mark: trunc sub trunc
-- statement:
--   The quantity of a decision: the difference of two evaluations is the sum BB.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/PaddedDescent/F/MarkLayers.lean#L327-L331
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/PaddedDescent/F/MarkLayers.lean#L327-L331

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

theorem PaddedDescent.F.Mark.trunc_sub_trunc {n w : ℕ} (C : Cl) {Λ L : Fml} {rest : List Fml} (h : Inv n w (Λ :: L :: rest))
    (hl : ((Λ :: L :: rest).getLastD []).length ≤ w) :
    trunc n w ((C :: Λ) :: L :: rest) - trunc n w (Λ :: L :: rest) = (BB n C Λ (L :: rest) : ℤ) := by sorry
