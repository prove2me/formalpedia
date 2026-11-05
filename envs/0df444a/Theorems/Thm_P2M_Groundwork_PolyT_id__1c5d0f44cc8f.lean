-- Prove2me | Theorems.Thm_P2M_Groundwork_PolyT_id__1c5d0f44cc8f
-- name    : P2M_Groundwork_PolyT_id__1c5d0f44cc8f
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-04T16:45:50.717517+00:00
-- url     : https://prove2.me/theorems/fa042bbf-48ae-4c3b-9013-25bb7ffa754e
-- title:
--   P2 M Groundwork Poly T id  1c5d0f44cc8f: P2 M Groundwork Poly T id  1c5d0f44cc8f
-- statement:
--   The P2 M Groundwork Poly T id  1c5d0f44cc8f construction uses the P2 M Groundwork Poly T id  1c5d0f44cc8f property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/machines/ToTuring/Closure/Basic.lean#L53-L54
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/machines/ToTuring/Closure/Basic.lean#L53-L54

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_ToTuring_PolyT
import Definitions.Def_ToTuring_EncLemmas
import Definitions.Def_ToTuring_Closure_Basic
import Theorems.Thm_P2M_Groundwork_PB_id__8af0b594aff4

set_option autoImplicit false
section
section
open Groundwork Groundwork.PolyT
open TM Enc
variable {α β γ δ ε : Type} [Enc α] [Enc β] [Enc γ] [Enc δ] [Enc ε]

theorem P2M_Groundwork_PolyT_id__1c5d0f44cc8f : PolyT (fun x : α => x) := by sorry

alias «Groundwork».«PolyT».«id'» := P2M_Groundwork_PolyT_id__1c5d0f44cc8f
