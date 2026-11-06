-- Prove2me | Theorems.Thm_SplitCount_round_iterate_map
-- name    : SplitCount.round_iterate_map
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T09:33:30.167737+00:00
-- url     : https://prove2.me/theorems/0b3b22fe-35ea-45a8-bcea-3aa3a0a7186c
-- title:
--   Split Count: round iterate map
-- statement:
--   If f commutes with the step functions, it commutes with any number of rounds of the walk.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/consequences/SplitCount/Tree.lean#L73-L77
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/consequences/SplitCount/Tree.lean#L73-L77

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_SplitCount_Defs
import Definitions.Def_SparsifyWidthK_Thresholds
import Definitions.Def_CountKSat_ProgC
import Definitions.Def_CountKSat_StepCount
import Definitions.Def_CountKSat_Walk
import Mathlib.Tactic.Tauto
import Definitions.Def_SplitCount_Tree
import Theorems.Thm_Groundwork_PolyT_map
attribute [local fun_prop] Groundwork.PolyT.map


set_option autoImplicit false
section
section
open SplitCount
open Groundwork Groundwork.Prog Groundwork.Sparsify WidthK.Prog CountKSat Eight Eight.Width
variable {σ ρ : Type} {s₁ : σ → Option (σ × σ)} {s₂ : ρ → Option (ρ × ρ)} {f : σ → ρ}

theorem SplitCount.round_iterate_map (h : ∀ x, s₂ (f x) = (s₁ x).map fun lh => (f lh.1, f lh.2)) (i : ℕ) (p : List σ × List σ) :
    (round s₂)^[i] (p.1.map f, p.2.map f) = (((round s₁)^[i] p).1.map f, ((round s₁)^[i] p).2.map f) := by sorry
