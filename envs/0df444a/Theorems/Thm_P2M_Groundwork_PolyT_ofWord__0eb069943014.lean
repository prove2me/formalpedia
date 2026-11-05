-- Prove2me | Theorems.Thm_P2M_Groundwork_PolyT_ofWord__0eb069943014
-- name    : P2M_Groundwork_PolyT_ofWord__0eb069943014
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-04T19:25:55.514002+00:00
-- url     : https://prove2.me/theorems/7aa90630-287b-4c6e-a727-bc1da2cabc11
-- title:
--   P2 M Groundwork Poly T of Word  0eb069943014: P2 M Groundwork Poly T of Word  0eb069943014
-- statement:
--   The number whose binary digits are the word, lowest digit first.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/machines/ToTuring/Lib/List2.lean#L118-L120
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/machines/ToTuring/Lib/List2.lean#L118-L120

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

theorem P2M_Groundwork_PolyT_ofWord__0eb069943014 {w : α → List Bool} (hw : PolyT w) :
    PolyT (fun x => ofWord (w x)) := by sorry

alias «Groundwork».«PolyT».«ofWord'» := P2M_Groundwork_PolyT_ofWord__0eb069943014
