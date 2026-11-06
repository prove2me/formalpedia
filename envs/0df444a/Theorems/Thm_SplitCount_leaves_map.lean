-- Prove2me | Theorems.Thm_SplitCount_leaves_map
-- name    : SplitCount.leaves_map
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T08:35:41.755438+00:00
-- url     : https://prove2.me/theorems/e928c740-d519-4ba4-85da-2c086baac31c
-- title:
--   Split Count: leaves map
-- statement:
--   If f commutes with the step functions, the leaves below f x are the images of the leaves below
--   x.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/consequences/SplitCount/Tree.lean#L45-L55
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/consequences/SplitCount/Tree.lean#L45-L55

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

theorem SplitCount.leaves_map (h : ∀ x, s₂ (f x) = (s₁ x).map fun lh => (f lh.1, f lh.2)) (d : ℕ) (x : σ) : leaves s₂ d (f x) = (leaves s₁ d x).map f := by sorry
