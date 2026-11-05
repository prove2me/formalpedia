-- Prove2me | Theorems.Thm_P2M_Groundwork_PolyT_inl__78f4b62d65a1
-- name    : P2M_Groundwork_PolyT_inl__78f4b62d65a1
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-04T16:46:18.348123+00:00
-- url     : https://prove2.me/theorems/888bce35-1f89-439c-a4ae-fa47cb15ec56
-- title:
--   P2 M Groundwork Poly T inl  78f4b62d65a1: P2 M Groundwork Poly T inl  78f4b62d65a1
-- statement:
--   The P2 M Groundwork Poly T inl  78f4b62d65a1 construction uses the P2 M Groundwork Poly T inl  78f4b62d65a1 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/machines/ToTuring/Closure/Basic.lean#L123-L124
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/machines/ToTuring/Closure/Basic.lean#L123-L124

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

theorem P2M_Groundwork_PolyT_inl__78f4b62d65a1 {f : α → β} (hf : PolyT f) : PolyT (fun x => (Sum.inl (f x) : β ⊕ γ)) := by sorry

alias «Groundwork».«PolyT».«inl'» := P2M_Groundwork_PolyT_inl__78f4b62d65a1
