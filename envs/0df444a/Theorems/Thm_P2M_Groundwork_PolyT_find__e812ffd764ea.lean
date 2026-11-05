-- Prove2me | Theorems.Thm_P2M_Groundwork_PolyT_find__e812ffd764ea
-- name    : P2M_Groundwork_PolyT_find__e812ffd764ea
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-04T17:34:36.106417+00:00
-- url     : https://prove2.me/theorems/a0241484-e9ca-439c-84a0-cab7c5623b78
-- title:
--   P2 M Groundwork Poly T find  e812ffd764ea: P2 M Groundwork Poly T find  e812ffd764ea
-- statement:
--   The P2 M Groundwork Poly T find  e812ffd764ea construction uses the P2 M Groundwork Poly T find  e812ffd764ea property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/machines/ToTuring/Lib/List1.lean#L183-L198
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/machines/ToTuring/Lib/List1.lean#L183-L198

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

theorem P2M_Groundwork_PolyT_find__e812ffd764ea {f : α → β → Bool} {l : α → List β} (hf : PolyT fun p : α × β => f p.1 p.2) (hl : PolyT l) :
    PolyT (fun x => (l x).find? (f x)) := by sorry

alias «Groundwork».«PolyT».«find?» := P2M_Groundwork_PolyT_find__e812ffd764ea
