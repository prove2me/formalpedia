-- Prove2me | Theorems.Thm_UniformInK_Step_toAddK
-- name    : UniformInK.Step.toAddK
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-04T20:40:55.671208+00:00
-- url     : https://prove2.me/theorems/1e906346-b5a2-4fa5-a94b-d5f85c7f8a3e
-- title:
--   Step: to Add K
-- statement:
--   A step in the sense of this folder is a step in the sense of
--   proof/sparsification/SparsifyWidthK/Defs.lean: take one-element sets Y.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/sparsification/UniformInK/Spars/Step.lean#L46-L53
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/sparsification/UniformInK/Spars/Step.lean#L46-L53

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_UniformInK_Spars_Defs
import Definitions.Def_SparsifyWidthK_Step
import Definitions.Def_SparsifyWidthK_Step
import Mathlib.Algebra.BigOperators.Group.Finset.Piecewise
import Mathlib.Tactic.SplitIfs
import Definitions.Def_UniformInK_Spars_Step
import Theorems.Thm_Groundwork_PolyT_all
attribute [local fun_prop] Groundwork.PolyT.all


set_option autoImplicit false
section
section
open UniformInK
open Finset Groundwork Groundwork.Sparsify WidthK
open UniformInK.Step
variable {α : Type*} [DecidableEq α]
variable {θ : ℕ → ℕ} {F A N : Finset (Finset α)} {r : ℕ} {a : ℕ → ℕ}

theorem UniformInK.Step.toAddK (hA : AddU θ F A r) : AddK (fun i => 2 * θ (i - 1)) F A r := by sorry
