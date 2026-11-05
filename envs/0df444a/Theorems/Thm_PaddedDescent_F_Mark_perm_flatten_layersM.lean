-- Prove2me | Theorems.Thm_PaddedDescent_F_Mark_perm_flatten_layersM
-- name    : PaddedDescent.F.Mark.perm_flatten_layersM
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T01:41:41.116617+00:00
-- url     : https://prove2.me/theorems/7e697f01-582e-4c4b-99c7-ac38b406f050
-- title:
--   Mark: perm flatten layers M
-- statement:
--   The clauses of the layers of ψ are the clauses of ψ, in some order.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/PaddedDescent/F/MarkLayers.lean#L483-L488
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/PaddedDescent/F/MarkLayers.lean#L483-L488

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
set_option autoImplicit false
section
section
open PaddedDescent PaddedDescent.F PaddedDescent.F.Mark
open Finset Groundwork.Prog
open Layers

theorem PaddedDescent.F.Mark.perm_flatten_layersM (n w R : ℕ) (ψ : Fml) : (layersM n w R ψ).flatten.Perm ψ := by sorry
