-- Prove2me | Theorems.Thm_PaddedDescent_F_Mark_Layers_drop_eq_cons
-- name    : PaddedDescent.F.Mark.Layers.drop_eq_cons
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T01:40:21.631528+00:00
-- url     : https://prove2.me/theorems/7d776f5a-ada1-4369-a2f1-1968f7e9e41f
-- title:
--   Layers: drop eq cons
-- statement:
--   The layers from number i on begin with layer number i.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/PaddedDescent/F/MarkLayers.lean#L85-L86
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/PaddedDescent/F/MarkLayers.lean#L85-L86

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

theorem PaddedDescent.F.Mark.Layers.drop_eq_cons {Ls : List Fml} {i : ℕ} (hi : i < Ls.length) : Ls.drop i = Ls.getD i [] :: Ls.drop (i + 1) := by sorry
