-- Prove2me | Theorems.Thm_UniformInK_Step_wsum_nextA_of_le
-- name    : UniformInK.Step.wsum_nextA_of_le
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-04T20:41:51.404226+00:00
-- url     : https://prove2.me/theorems/75a5aa41-daac-4b53-b957-fc94ac2a613b
-- title:
--   Step: wsum next A of le
-- statement:
--   The weighted counts below size i do not change if i ≤ r.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/sparsification/UniformInK/Spars/Step.lean#L56-L60
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/sparsification/UniformInK/Spars/Step.lean#L56-L60

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

theorem UniformInK.Step.wsum_nextA_of_le (w a : ℕ → ℕ) (c : ℕ) {i r : ℕ} (hi : i ≤ r) :
    ∑ i' ∈ range i, w i' * nextA a r c i' = ∑ i' ∈ range i, w i' * a i' := by sorry
