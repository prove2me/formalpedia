-- Prove2me | Theorems.Thm_PaddedDescent_F_Mark_Layers_getLastD_drop
-- name    : PaddedDescent.F.Mark.Layers.getLastD_drop
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T01:40:15.401075+00:00
-- url     : https://prove2.me/theorems/ad127b64-7bcb-41fd-9b3c-fa3b6f430aea
-- title:
--   Layers: get Last D drop
-- statement:
--   The layers from number i on have the same last layer.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/PaddedDescent/F/MarkLayers.lean#L89-L92
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/PaddedDescent/F/MarkLayers.lean#L89-L92

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
open PaddedDescent.F.Mark.Layers

theorem PaddedDescent.F.Mark.Layers.getLastD_drop {Ls : List Fml} {i : ℕ} (hi : i < Ls.length) : (Ls.drop i).getLastD [] = Ls.getLastD [] := by sorry
