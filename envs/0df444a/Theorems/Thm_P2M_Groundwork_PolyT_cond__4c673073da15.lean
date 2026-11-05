-- Prove2me | Theorems.Thm_P2M_Groundwork_PolyT_cond__4c673073da15
-- name    : P2M_Groundwork_PolyT_cond__4c673073da15
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-04T16:47:35.669352+00:00
-- url     : https://prove2.me/theorems/c46c4145-5744-4ede-b4b2-f918e8f2b321
-- title:
--   P2 M Groundwork Poly T cond  4c673073da15: P2 M Groundwork Poly T cond  4c673073da15
-- statement:
--   Case distinction on a Boolean c x; both branches see the context x.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/machines/ToTuring/Closure/Cases.lean#L147-L151
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/machines/ToTuring/Closure/Cases.lean#L147-L151

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_ToTuring_Closure_Basic
import Definitions.Def_ToTuring_Closure_Cases
set_option autoImplicit false
section
section
open Groundwork Groundwork.PolyT
open TM Turing
variable {α β γ δ ε : Type} [Enc α] [Enc β] [Enc γ] [Enc δ] [Enc ε]

theorem P2M_Groundwork_PolyT_cond__4c673073da15 {c : α → Bool} {f g : α → β} (hc : PolyT c) (hf : PolyT f) (hg : PolyT g) :
    PolyT (fun x => bif c x then f x else g x) := by sorry

alias «Groundwork».«PolyT».«cond'» := P2M_Groundwork_PolyT_cond__4c673073da15
