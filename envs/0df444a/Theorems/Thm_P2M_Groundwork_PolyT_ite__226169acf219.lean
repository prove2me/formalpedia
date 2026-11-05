-- Prove2me | Theorems.Thm_P2M_Groundwork_PolyT_ite__226169acf219
-- name    : P2M_Groundwork_PolyT_ite__226169acf219
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-04T16:47:27.050282+00:00
-- url     : https://prove2.me/theorems/d2e5239a-87ea-4985-a7bb-dbbe254ffd3e
-- title:
--   P2 M Groundwork Poly T ite  226169acf219: P2 M Groundwork Poly T ite  226169acf219
-- statement:
--   The same for `if … then … else` on a decidable proposition c x.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/machines/ToTuring/Closure/Cases.lean#L153-L155
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/machines/ToTuring/Closure/Cases.lean#L153-L155

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

theorem P2M_Groundwork_PolyT_ite__226169acf219 {c : α → Prop} [DecidablePred c] {f g : α → β} (hc : PolyT fun x => decide (c x)) (hf : PolyT f)
    (hg : PolyT g) : PolyT (fun x => if c x then f x else g x) := by sorry

alias «Groundwork».«PolyT».«ite'» := P2M_Groundwork_PolyT_ite__226169acf219
