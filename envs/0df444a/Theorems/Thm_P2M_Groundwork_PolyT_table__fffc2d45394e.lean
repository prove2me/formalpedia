-- Prove2me | Theorems.Thm_P2M_Groundwork_PolyT_table__fffc2d45394e
-- name    : P2M_Groundwork_PolyT_table__fffc2d45394e
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-04T17:27:37.463366+00:00
-- url     : https://prove2.me/theorems/cc017a4d-93c6-4d6d-9280-2a34bc96a589
-- title:
--   P2 M Groundwork Poly T table  fffc2d45394e: P2 M Groundwork Poly T table  fffc2d45394e
-- statement:
--   A table with two arguments.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/machines/ToTuring/Lib/Table.lean#L59-L61
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/machines/ToTuring/Lib/Table.lean#L59-L61

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_ToTuring_Lib_Bool
import Mathlib.Data.Fintype.Card
import Mathlib.Data.Fintype.Prod
import Definitions.Def_ToTuring_Lib_Table
set_option autoImplicit false
section
section
open Groundwork Groundwork.PolyT
variable {α β γ δ ε ζ : Type} [Enc α] [Enc β] [Enc γ] [Enc δ] [Enc ε] [Enc ζ]

theorem P2M_Groundwork_PolyT_table__fffc2d45394e [Finite β] [DecidableEq β] [EqT β] [Finite γ] [DecidableEq γ] [EqT γ] (F : β → γ → ζ) {f : α → β} {g : α → γ}
    (hf : PolyT f) (hg : PolyT g) : PolyT fun x => F (f x) (g x) := by sorry

alias «Groundwork».«PolyT».«table₂» := P2M_Groundwork_PolyT_table__fffc2d45394e
