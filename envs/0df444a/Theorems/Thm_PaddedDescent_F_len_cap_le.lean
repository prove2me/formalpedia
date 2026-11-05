-- Prove2me | Theorems.Thm_PaddedDescent_F_len_cap_le
-- name    : PaddedDescent.F.len_cap_le
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-04T20:14:24.429401+00:00
-- url     : https://prove2.me/theorems/1e5fa824-917a-4ab2-aef9-d76aeed9ecd8
-- title:
--   F: len cap le
-- statement:
--   The F construction uses the len cap le property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/PaddedDescent/F/Fuel.lean#L77-L78
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/PaddedDescent/F/Fuel.lean#L77-L78

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_ToTuring_Lib_Int
import Definitions.Def_ToTuring_Lib_List3
import Definitions.Def_ToTuring_Lib_List2
import Definitions.Def_ToTuring_Lib_Unary
import Definitions.Def_ToTuring_Lib_Nat2
import Definitions.Def_ToTuring_Lib_Nat1b
import Definitions.Def_PaddedDescent_F_Fuel
import Theorems.Thm_Groundwork_PolyT_length
attribute [local fun_prop] Groundwork.PolyT.length


set_option autoImplicit false
section
section
open PaddedDescent PaddedDescent.F
open Groundwork

theorem PaddedDescent.F.len_cap_le {γ : Type} [Enc γ] (pad : U) (d x : γ) : len (cap pad d x) ≤ pad.length + len d := by sorry
