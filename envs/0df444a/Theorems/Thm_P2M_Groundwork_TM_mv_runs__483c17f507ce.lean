-- Prove2me | Theorems.Thm_P2M_Groundwork_TM_mv_runs__483c17f507ce
-- name    : P2M_Groundwork_TM_mv_runs__483c17f507ce
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-04T15:55:21.298845+00:00
-- url     : https://prove2.me/theorems/24eeb89b-3294-4764-a9ee-8612a6d79db7
-- title:
--   P2 M Groundwork TM mv runs  483c17f507ce: P2 M Groundwork TM mv runs  483c17f507ce
-- statement:
--   The way back: a mirrored item becomes the item.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/machines/ToTuring/TM/Move.lean#L253-L258
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/machines/ToTuring/TM/Move.lean#L253-L258

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_ToTuring_TM_Rename
import Definitions.Def_ToTuring_TM_Stacks
import Definitions.Def_ToTuring_TM_Move
set_option autoImplicit false
section
section
open Groundwork Groundwork.TM
open Turing

theorem P2M_Groundwork_TM_mv_runs__483c17f507ce {i j : Stk} (hij : i ≠ j) (hi : i ≠ .cnt) (hj : j ≠ .cnt) (x : V) {S : Stk → List Sym} {W : List Sym}
    (h : S i = mirror (code x) ++ W) :
    (mv i j).Runs none S ((code x).length + 1) (Function.update (Function.update S i W) j (code x ++ S j)) := by sorry

alias «Groundwork».«TM».«mv_runs'» := P2M_Groundwork_TM_mv_runs__483c17f507ce
