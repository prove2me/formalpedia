-- Prove2me | Theorems.Thm_P2M_Groundwork_PolyT_some__e6a32bd6af45
-- name    : P2M_Groundwork_PolyT_some__e6a32bd6af45
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-04T16:46:09.927378+00:00
-- url     : https://prove2.me/theorems/cc6ec298-ccd3-4d6c-b14c-7368eca52862
-- title:
--   P2 M Groundwork Poly T some  e6a32bd6af45: P2 M Groundwork Poly T some  e6a32bd6af45
-- statement:
--   The P2 M Groundwork Poly T some  e6a32bd6af45 construction uses the P2 M Groundwork Poly T some  e6a32bd6af45 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/machines/ToTuring/Closure/Basic.lean#L121-L122
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/machines/ToTuring/Closure/Basic.lean#L121-L122

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

theorem P2M_Groundwork_PolyT_some__e6a32bd6af45 {f : α → β} (hf : PolyT f) : PolyT (fun x => some (f x)) := by sorry

alias «Groundwork».«PolyT».«some'» := P2M_Groundwork_PolyT_some__e6a32bd6af45
