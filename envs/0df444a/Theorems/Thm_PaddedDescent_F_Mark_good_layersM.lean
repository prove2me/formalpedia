-- Prove2me | Theorems.Thm_PaddedDescent_F_Mark_good_layersM
-- name    : PaddedDescent.F.Mark.good_layersM
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T01:41:26.852807+00:00
-- url     : https://prove2.me/theorems/1b3b4fcb-f33e-4b62-b9e7-1d80942f7590
-- title:
--   Mark: good layers M
-- statement:
--   The layers of ψ are good.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/PaddedDescent/F/MarkLayers.lean#L435-L436
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/PaddedDescent/F/MarkLayers.lean#L435-L436

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

theorem PaddedDescent.F.Mark.good_layersM {n w : ℕ} (hw : n + 2 ≤ w) {R : ℕ} {ψ : Fml} (hR : 2 ^ R * ψ.length + 5 * 3 ^ R ≤ 3 ^ R * w) :
    Good n w (layersM n w R ψ) := by sorry
