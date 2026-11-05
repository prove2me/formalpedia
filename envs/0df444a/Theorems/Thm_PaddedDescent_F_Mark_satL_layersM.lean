-- Prove2me | Theorems.Thm_PaddedDescent_F_Mark_satL_layersM
-- name    : PaddedDescent.F.Mark.satL_layersM
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T03:29:22.034344+00:00
-- url     : https://prove2.me/theorems/f96cb937-c57f-405e-9291-36b284828bb8
-- title:
--   Mark: sat L layers M
-- statement:
--   The layers of ψ are satisfied exactly if no clause of ψ is violated.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/PaddedDescent/F/MarkLayers.lean#L415-L424
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/PaddedDescent/F/MarkLayers.lean#L415-L424

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

theorem PaddedDescent.F.Mark.satL_layersM (n w R : ℕ) (σ : ℕ → Bool) (ψ : Fml) : satL σ (layersM n w R ψ) ↔ nvio σ ψ = 0 := by sorry
