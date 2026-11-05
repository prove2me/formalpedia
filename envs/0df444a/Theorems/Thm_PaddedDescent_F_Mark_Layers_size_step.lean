-- Prove2me | Theorems.Thm_PaddedDescent_F_Mark_Layers_size_step
-- name    : PaddedDescent.F.Mark.Layers.size_step
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T03:30:27.503348+00:00
-- url     : https://prove2.me/theorems/3f67217f-38d8-4c25-978f-3c71528ffd8d
-- title:
--   Layers: size step
-- statement:
--   3^κ ≤ 2^N gives 3κ ≤ 2N + 3, because 8 ≤ 9.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/PaddedDescent/F/MarkLayers.lean#L76-L82
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/PaddedDescent/F/MarkLayers.lean#L76-L82

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

theorem PaddedDescent.F.Mark.Layers.size_step (κ N : ℕ) (h : 3 ^ κ ≤ 2 ^ N) : 3 * κ ≤ 2 * N + 3 := by sorry
