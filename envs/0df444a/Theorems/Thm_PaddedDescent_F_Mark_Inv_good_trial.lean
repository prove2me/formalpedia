-- Prove2me | Theorems.Thm_PaddedDescent_F_Mark_Inv_good_trial
-- name    : PaddedDescent.F.Mark.Inv.good_trial
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T01:40:47.50236+00:00
-- url     : https://prove2.me/theorems/3d40b712-282f-4bc2-91a1-aa6ba84f3f94
-- title:
--   Inv: good trial
-- statement:
--   The layers with C on trial in the first of them are good.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/PaddedDescent/F/MarkLayers.lean#L319-L324
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/PaddedDescent/F/MarkLayers.lean#L319-L324

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

theorem PaddedDescent.F.Mark.Inv.good_trial {n w : ℕ} (C : Cl) {Λ L : Fml} {rest : List Fml} (h : Inv n w (Λ :: L :: rest))
    (hl : ((Λ :: L :: rest).getLastD []).length ≤ w) : Good n w ((C :: Λ) :: L :: rest) := by sorry
