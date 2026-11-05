-- Prove2me | Theorems.Thm_PaddedDescent_F_sumF_eq
-- name    : PaddedDescent.F.sumF_eq
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-04T19:50:32.530878+00:00
-- url     : https://prove2.me/theorems/d60de93d-75fa-468d-babc-982b6f50c0bc
-- title:
--   F: sum F eq
-- statement:
--   The F construction uses the sum F eq property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/PaddedDescent/F/Fuel.lean#L54-L64
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/PaddedDescent/F/Fuel.lean#L54-L64

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

theorem PaddedDescent.F.sumF_eq {N : ℕ} {pad : U} (h : N ≤ pad.length) (f : ℕ → ℤ) :
    sumF N pad f = ∑ y ∈ Finset.range N, f y := by sorry
