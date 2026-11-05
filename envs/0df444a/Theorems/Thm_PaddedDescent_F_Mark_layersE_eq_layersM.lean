-- Prove2me | Theorems.Thm_PaddedDescent_F_Mark_layersE_eq_layersM
-- name    : PaddedDescent.F.Mark.layersE_eq_layersM
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T03:30:16.688559+00:00
-- url     : https://prove2.me/theorems/5964402e-08a4-4b05-8179-7a5ee3d7fa67
-- title:
--   Mark: layers E eq layers M
-- statement:
--   If the evaluation is exact on the lists on which it is used, the layers by evaluations are the
--   layers by sums.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/PaddedDescent/F/MarkLayers.lean#L496-L529
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/PaddedDescent/F/MarkLayers.lean#L496-L529

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

theorem PaddedDescent.F.Mark.layersE_eq_layersM {n w R : ℕ} {ev : List Fml → ℤ} {ψ : Fml} (hw : n + 2 ≤ w) (hR : 2 ^ R * ψ.length + 5 * 3 ^ R ≤ 3 ^ R * w)
    (hev : ∀ Ls, Asked n w R ψ Ls → ev Ls = trunc n w Ls) : ∀ ψ' : Fml, ψ' <+: ψ → layersE ev w R ψ' = layersM n w R ψ' := by sorry
