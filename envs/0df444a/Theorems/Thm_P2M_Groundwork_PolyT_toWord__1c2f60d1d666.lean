-- Prove2me | Theorems.Thm_P2M_Groundwork_PolyT_toWord__1c2f60d1d666
-- name    : P2M_Groundwork_PolyT_toWord__1c2f60d1d666
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-04T19:26:46.538199+00:00
-- url     : https://prove2.me/theorems/2f6b37b3-4eba-4f95-8aea-fe3dffcd74e6
-- title:
--   P2 M Groundwork Poly T to Word  1c2f60d1d666: P2 M Groundwork Poly T to Word  1c2f60d1d666
-- statement:
--   The n lowest binary digits of y, lowest digit first; the length n must be given in unary.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/machines/ToTuring/Lib/List2.lean#L128-L132
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/machines/ToTuring/Lib/List2.lean#L128-L132

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

theorem P2M_Groundwork_PolyT_toWord__1c2f60d1d666 {n y : α → ℕ} (hn : Unary n) (hy : PolyT y) :
    PolyT (fun x => toWord (n x) (y x)) := by sorry

alias «Groundwork».«PolyT».«toWord'» := P2M_Groundwork_PolyT_toWord__1c2f60d1d666
