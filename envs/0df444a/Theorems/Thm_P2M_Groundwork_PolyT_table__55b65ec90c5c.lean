-- Prove2me | Theorems.Thm_P2M_Groundwork_PolyT_table__55b65ec90c5c
-- name    : P2M_Groundwork_PolyT_table__55b65ec90c5c
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-04T17:28:03.509863+00:00
-- url     : https://prove2.me/theorems/927dd8f9-cd0b-43f8-bb7f-e68d81e43585
-- title:
--   P2 M Groundwork Poly T table  55b65ec90c5c: P2 M Groundwork Poly T table  55b65ec90c5c
-- statement:
--   A table with three arguments.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/machines/ToTuring/Lib/Table.lean#L64-L67
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/machines/ToTuring/Lib/Table.lean#L64-L67

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

theorem P2M_Groundwork_PolyT_table__55b65ec90c5c [Finite β] [DecidableEq β] [EqT β] [Finite γ] [DecidableEq γ] [EqT γ] [Finite δ] [DecidableEq δ] [EqT δ]
    (F : β → γ → δ → ζ) {f : α → β} {g : α → γ} {h : α → δ} (hf : PolyT f) (hg : PolyT g) (hh : PolyT h) :
    PolyT fun x => F (f x) (g x) (h x) := by sorry

alias «Groundwork».«PolyT».«table₃» := P2M_Groundwork_PolyT_table__55b65ec90c5c
