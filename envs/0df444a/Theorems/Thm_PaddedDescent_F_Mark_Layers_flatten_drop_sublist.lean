-- Prove2me | Theorems.Thm_PaddedDescent_F_Mark_Layers_flatten_drop_sublist
-- name    : PaddedDescent.F.Mark.Layers.flatten_drop_sublist
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T03:29:44.899981+00:00
-- url     : https://prove2.me/theorems/53edaa10-8eab-4eef-b5a9-5a66f0745c95
-- title:
--   Layers: flatten drop sublist
-- statement:
--   The clauses of the layers from number i on are among the clauses of all layers.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/PaddedDescent/F/MarkLayers.lean#L95-L96
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/PaddedDescent/F/MarkLayers.lean#L95-L96

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
open PaddedDescent.F.Mark.Layers

theorem PaddedDescent.F.Mark.Layers.flatten_drop_sublist (Ls : List Fml) (i : ℕ) : (Ls.drop i).flatten.Sublist Ls.flatten := by sorry
