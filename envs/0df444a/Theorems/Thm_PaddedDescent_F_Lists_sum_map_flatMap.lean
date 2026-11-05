-- Prove2me | Theorems.Thm_PaddedDescent_F_Lists_sum_map_flatMap
-- name    : PaddedDescent.F.Lists.sum_map_flatMap
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-04T16:44:18.281667+00:00
-- url     : https://prove2.me/theorems/fc44edea-03a1-4a68-a3aa-cec0001e4051
-- title:
--   Lists: sum map flat Map
-- statement:
--   The sum of z over w.flatMap e is the sum, over the members a of w, of the sums of z over e a.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/PaddedDescent/F/LenList.lean#L50-L54
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/PaddedDescent/F/LenList.lean#L50-L54

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_ToTuring_EncLemmas
import Definitions.Def_PaddedDescent_F_LenList
set_option autoImplicit false
section
section
open PaddedDescent PaddedDescent.F PaddedDescent.F.Lists
open Groundwork

theorem PaddedDescent.F.Lists.sum_map_flatMap {α β : Type*} (w : List α) (e : α → List β) (z : β → ℤ) :
    ((w.flatMap e).map z).sum = (w.map fun a => ((e a).map z).sum).sum := by sorry
