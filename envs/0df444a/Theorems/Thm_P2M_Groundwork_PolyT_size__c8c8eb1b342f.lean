-- Prove2me | Theorems.Thm_P2M_Groundwork_PolyT_size__c8c8eb1b342f
-- name    : P2M_Groundwork_PolyT_size__c8c8eb1b342f
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-04T18:36:35.499019+00:00
-- url     : https://prove2.me/theorems/6f03e8f5-dd57-4e1d-a16f-4ccd03a85d8d
-- title:
--   P2 M Groundwork Poly T size  c8c8eb1b342f: P2 M Groundwork Poly T size  c8c8eb1b342f
-- statement:
--   The number of binary digits of a number: the length of its list of digits.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/machines/ToTuring/Lib/Nat1b.lean#L96-L98
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/machines/ToTuring/Lib/Nat1b.lean#L96-L98

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_ToTuring_Lib_Nat1
import Definitions.Def_ToTuring_Lib_Nat1b
set_option autoImplicit false
section
section
open Groundwork Groundwork.PolyT
variable {α β γ δ ε : Type} [Enc α] [Enc β] [Enc γ] [Enc δ] [Enc ε]

theorem P2M_Groundwork_PolyT_size__c8c8eb1b342f {f : α → ℕ} (hf : PolyT f) :
    PolyT (fun x => Nat.size (f x)) := by sorry

alias «Groundwork».«PolyT».«size'» := P2M_Groundwork_PolyT_size__c8c8eb1b342f
