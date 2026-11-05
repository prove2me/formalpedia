-- Prove2me | Theorems.Thm_PaddedDescent_F_rng_eq
-- name    : PaddedDescent.F.rng_eq
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-04T19:51:08.416005+00:00
-- url     : https://prove2.me/theorems/51253262-69ea-4a2a-82f4-c04ce1e41746
-- title:
--   F: rng eq
-- statement:
--   The F construction uses the rng eq property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/PaddedDescent/F/Fuel.lean#L51-L52
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/PaddedDescent/F/Fuel.lean#L51-L52

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

theorem PaddedDescent.F.rng_eq {pad : U} {q : ℕ} (h : q ≤ pad.length) : rng pad q = List.range q := by sorry
