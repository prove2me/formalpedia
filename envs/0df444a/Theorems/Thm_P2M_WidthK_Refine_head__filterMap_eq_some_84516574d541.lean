-- Prove2me | Theorems.Thm_P2M_WidthK_Refine_head__filterMap_eq_some_84516574d541
-- name    : P2M_WidthK_Refine_head__filterMap_eq_some_84516574d541
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-04T20:30:32.594072+00:00
-- url     : https://prove2.me/theorems/22aff79a-0c6c-4360-854e-4d74e4dfb6aa
-- title:
--   P2 M Width K Refine head  filter Map eq some 84516574d541: P2 M Width K Refine head  filter Map eq some 84516574d541
-- statement:
--   If `(l.filterMap f).head?` is `some b`, then b is the result of f at some entry of l, and f has
--   no result at the entries before it.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/sparsification/SparsifyWidthK/Refine.lean#L193-L209
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/sparsification/SparsifyWidthK/Refine.lean#L193-L209

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_SparsifyWidthK_Interfaces
import Definitions.Def_StepMachines_Math_SparsifyProg
import Definitions.Def_StepMachines_Math_SparsifyProg
import Mathlib.Data.List.Nodup
import Definitions.Def_SparsifyWidthK_Refine
import Theorems.Thm_Groundwork_PolyT_all
import Theorems.Thm_Groundwork_PolyT_filterMap
attribute [local fun_prop] Groundwork.PolyT.all
attribute [local fun_prop] Groundwork.PolyT.filterMap


set_option autoImplicit false
section
open WidthK WidthK.Refine
open Finset Groundwork Groundwork.Sparsify WidthK.Prog

theorem P2M_WidthK_Refine_head__filterMap_eq_some_84516574d541 {α β : Type*} {f : α → Option β} {l : List α} {b : β}
    (h : (l.filterMap f).head? = some b) : ∃ l₁ a l₂, l = l₁ ++ a :: l₂ ∧ f a = some b ∧ ∀ x ∈ l₁, f x = none := by sorry

alias «WidthK».«Refine».«head?_filterMap_eq_some» := P2M_WidthK_Refine_head__filterMap_eq_some_84516574d541
