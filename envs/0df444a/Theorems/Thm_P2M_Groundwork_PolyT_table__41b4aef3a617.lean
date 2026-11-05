-- Prove2me | Theorems.Thm_P2M_Groundwork_PolyT_table__41b4aef3a617
-- name    : P2M_Groundwork_PolyT_table__41b4aef3a617
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-04T17:27:38.196298+00:00
-- url     : https://prove2.me/theorems/f43f39d5-5a8e-4eb6-9dda-ff7e284d8212
-- title:
--   P2 M Groundwork Poly T table  41b4aef3a617: P2 M Groundwork Poly T table  41b4aef3a617
-- statement:
--   A table after a polynomial-time argument.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/machines/ToTuring/Lib/Table.lean#L55-L56
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/machines/ToTuring/Lib/Table.lean#L55-L56

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

theorem P2M_Groundwork_PolyT_table__41b4aef3a617 [Finite β] [DecidableEq β] [EqT β] (F : β → ζ) {f : α → β} (hf : PolyT f) : PolyT fun x => F (f x) := by sorry

alias «Groundwork».«PolyT».«table₁» := P2M_Groundwork_PolyT_table__41b4aef3a617
