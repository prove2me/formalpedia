-- Prove2me | Theorems.Thm_P2M_Groundwork_PolyT_chunks__bc5b8682856d
-- name    : P2M_Groundwork_PolyT_chunks__bc5b8682856d
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-04T19:26:22.731768+00:00
-- url     : https://prove2.me/theorems/a474a6f8-d9e6-40a3-8d48-e1238ea075f9
-- title:
--   P2 M Groundwork Poly T chunks  bc5b8682856d: P2 M Groundwork Poly T chunks  bc5b8682856d
-- statement:
--   Cutting a word into consecutive pieces of the given lengths.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/machines/ToTuring/Lib/List2.lean#L143-L154
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/machines/ToTuring/Lib/List2.lean#L143-L154

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_ToTuring_Lib_Nat1b
import Definitions.Def_StepMachines_Prog_Chunks
import Definitions.Def_ToTuring_Lib_List2
set_option autoImplicit false
section
section
open Groundwork Groundwork.PolyT
variable {α β γ δ ε : Type} [Enc α] [Enc β] [Enc γ] [Enc δ] [Enc ε]

theorem P2M_Groundwork_PolyT_chunks__bc5b8682856d {cs : α → List ℕ} {w : α → List Bool} (hc : PolyT cs) (hw : PolyT w) :
    PolyT (fun x => chunks (cs x) (w x)) := by sorry

alias «Groundwork».«PolyT».«chunks'» := P2M_Groundwork_PolyT_chunks__bc5b8682856d
