-- Prove2me | Theorems.Thm_PaddedDescent_F_Mark_last_layersM_le
-- name    : PaddedDescent.F.Mark.last_layersM_le
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T01:40:43.339938+00:00
-- url     : https://prove2.me/theorems/c331f8e7-55ae-4619-b4a8-8b743a045ef2
-- title:
--   Mark: last layers M le
-- statement:
--   If 2^R·|ψ| + 5·3^R ≤ 3^R·c, the last layer has at most c clauses.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/PaddedDescent/F/MarkLayers.lean#L427-L432
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/PaddedDescent/F/MarkLayers.lean#L427-L432

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

theorem PaddedDescent.F.Mark.last_layersM_le {n w : ℕ} (hw : n + 2 ≤ w) {R c : ℕ} {ψ : Fml} (hR : 2 ^ R * ψ.length + 5 * 3 ^ R ≤ 3 ^ R * c) :
    ((layersM n w R ψ).getLastD []).length ≤ c := by sorry
