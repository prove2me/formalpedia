-- Prove2me | Theorems.Thm_PaddedDescent_F_cap_eq
-- name    : PaddedDescent.F.cap_eq
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-04T19:47:21.617077+00:00
-- url     : https://prove2.me/theorems/b41700f5-0890-46d4-8e25-2339977d2975
-- title:
--   F: cap eq
-- statement:
--   The F construction uses the cap eq property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/PaddedDescent/F/Fuel.lean#L75-L75
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/PaddedDescent/F/Fuel.lean#L75-L75

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

theorem PaddedDescent.F.cap_eq {γ : Type} [Enc γ] {pad : U} {d x : γ} (h : len x ≤ pad.length) : cap pad d x = x := by sorry
