-- Prove2me | Theorems.Thm_PaddedDescent_F_Mark_length_flatten_layersM
-- name    : PaddedDescent.F.Mark.length_flatten_layersM
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T03:30:25.80308+00:00
-- url     : https://prove2.me/theorems/7fd9fb23-e44d-4f07-93ba-5d512eb21e44
-- title:
--   Mark: length flatten layers M
-- statement:
--   The layers of ψ have as many clauses as ψ.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/PaddedDescent/F/MarkLayers.lean#L409-L412
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/PaddedDescent/F/MarkLayers.lean#L409-L412

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

theorem PaddedDescent.F.Mark.length_flatten_layersM (n w R : ℕ) (ψ : Fml) : (layersM n w R ψ).flatten.length = ψ.length := by sorry
