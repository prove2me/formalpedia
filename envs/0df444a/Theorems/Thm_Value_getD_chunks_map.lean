-- Prove2me | Theorems.Thm_Value_getD_chunks_map
-- name    : Value.getD_chunks_map
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T03:56:50.549206+00:00
-- url     : https://prove2.me/theorems/a53eadac-9788-4f4c-92fb-1dc312ad2cc6
-- title:
--   Value: get D chunks map
-- statement:
--   A string w is cut into blocks of the lengths f j, j in the list e. The block of the index i
--   begins after the blocks of the indices before i, and has f i positions.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/networks/Value/Words.lean#L71-L82
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/networks/Value/Words.lean#L71-L82

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_Value_Defs
import Definitions.Def_Value_Words
import Theorems.Thm_Groundwork_PolyT_idxOf
import Theorems.Thm_Groundwork_PolyT_map
import Theorems.Thm_Groundwork_PolyT_sum
attribute [local fun_prop] Groundwork.PolyT.idxOf
attribute [local fun_prop] Groundwork.PolyT.map
attribute [local fun_prop] Groundwork.PolyT.sum


set_option autoImplicit false
section
section
open Value
open Groundwork Finset

theorem Value.getD_chunks_map {ι : Type*} [BEq ι] [LawfulBEq ι] (f : ι → ℕ) (e : List ι) (w d : List Bool) {i : ι} (hi : i ∈ e) :
    (chunks (e.map f) w).getD (e.idxOf i) d = (w.drop ((e.map f).take (e.idxOf i)).sum).take (f i) := by sorry
