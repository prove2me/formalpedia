-- Prove2me | Theorems.Thm_P2M_Groundwork_PolyT_cons__3a60f43a3b86
-- name    : P2M_Groundwork_PolyT_cons__3a60f43a3b86
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-04T16:46:15.779464+00:00
-- url     : https://prove2.me/theorems/f7fc432c-e844-4afa-8230-1ad47f5f7424
-- title:
--   P2 M Groundwork Poly T cons  3a60f43a3b86: P2 M Groundwork Poly T cons  3a60f43a3b86
-- statement:
--   The P2 M Groundwork Poly T cons  3a60f43a3b86 construction uses the P2 M Groundwork Poly T cons  3a60f43a3b86 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/machines/ToTuring/Closure/Basic.lean#L127-L128
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/machines/ToTuring/Closure/Basic.lean#L127-L128

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_ToTuring_PolyT
import Definitions.Def_ToTuring_EncLemmas
import Definitions.Def_ToTuring_Closure_Basic
set_option autoImplicit false
section
section
open Groundwork Groundwork.PolyT
open TM Enc
variable {α β γ δ ε : Type} [Enc α] [Enc β] [Enc γ] [Enc δ] [Enc ε]

theorem P2M_Groundwork_PolyT_cons__3a60f43a3b86 {f : α → β} {l : α → List β} (hf : PolyT f) (hl : PolyT l) : PolyT (fun x => f x :: l x) := by sorry

alias «Groundwork».«PolyT».«cons'» := P2M_Groundwork_PolyT_cons__3a60f43a3b86
