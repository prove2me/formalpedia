-- Prove2me | Theorems.Thm_P2M_Groundwork_PolyT_comp__e2daf044ba87
-- name    : P2M_Groundwork_PolyT_comp__e2daf044ba87
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-04T17:34:56.085061+00:00
-- url     : https://prove2.me/theorems/7012ef25-5c20-4955-906e-c22963449689
-- title:
--   P2 M Groundwork Poly T comp  e2daf044ba87: P2 M Groundwork Poly T comp  e2daf044ba87
-- statement:
--   A two-argument function after polynomial-time arguments.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/machines/ToTuring/Lib/List1.lean#L38-L40
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/machines/ToTuring/Lib/List1.lean#L38-L40

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_ToTuring_Lib_Bool
import Definitions.Def_ToTuring_Lib_List1
set_option autoImplicit false
section
section
open Groundwork Groundwork.PolyT
variable {α β γ δ ε : Type} [Enc α] [Enc β] [Enc γ] [Enc δ] [Enc ε]

theorem P2M_Groundwork_PolyT_comp__e2daf044ba87 {f : α → β → γ} {a : δ → α} {b : δ → β} (hf : PolyT fun p : α × β => f p.1 p.2) (ha : PolyT a)
    (hb : PolyT b) : PolyT fun x => f (a x) (b x) := by sorry

alias «Groundwork».«PolyT».«comp₂» := P2M_Groundwork_PolyT_comp__e2daf044ba87
