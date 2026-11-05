-- Prove2me | Theorems.Thm_PaddedDescent_F_Expand_filterMap_spec
-- name    : PaddedDescent.F.Expand.filterMap_spec
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T03:28:37.081379+00:00
-- url     : https://prove2.me/theorems/b46bb2cb-7ab9-4b8a-b476-0a136902b5f1
-- title:
--   Expand: filter Map spec
-- statement:
--   A filterMap all of whose values are `some`.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/PaddedDescent/F/Expand.lean#L29-L40
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/PaddedDescent/F/Expand.lean#L29-L40

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_PaddedDescent_F_SideF
import Definitions.Def_PaddedDescent_F_Expand
import Theorems.Thm_Groundwork_PolyT_filterMap
import Theorems.Thm_Groundwork_PolyT_length
import Theorems.Thm_Groundwork_PolyT_map
import Theorems.Thm_Groundwork_PolyT_sum
attribute [local fun_prop] Groundwork.PolyT.filterMap
attribute [local fun_prop] Groundwork.PolyT.length
attribute [local fun_prop] Groundwork.PolyT.map
attribute [local fun_prop] Groundwork.PolyT.sum


set_option autoImplicit false
section
section
open PaddedDescent PaddedDescent.F PaddedDescent.F.Expand
open Groundwork Groundwork.Prog Groundwork.Grid Finset

theorem PaddedDescent.F.Expand.filterMap_spec {α β : Type} {f : α → Option β} {z : β → ℤ} {v : α → ℤ} {Q : β → Prop} :
    ∀ (l : List α), (∀ a ∈ l, ∃ b, f a = some b ∧ z b = v a ∧ Q b) →
      ((l.filterMap f).map z).sum = (l.map v).sum ∧ (∀ b ∈ l.filterMap f, Q b) ∧ (l.filterMap f).length = l.length
  := by sorry
