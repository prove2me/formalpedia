-- Prove2me | Theorems.Thm_PaddedDescent_F_Descend_descend_list
-- name    : PaddedDescent.F.Descend.descend_list
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T03:24:58.647212+00:00
-- url     : https://prove2.me/theorems/8a84118e-6478-4758-a278-a6d387caa7f9
-- title:
--   Descend: descend list
-- statement:
--   `StD` for a work list: the steps of the schedule followed by brute force do not change the sum
--   of Z over the list.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/PaddedDescent/F/Descend.lean#L57-L81
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/PaddedDescent/F/Descend.lean#L57-L81

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_PaddedDescent_F_Interfaces
import Definitions.Def_PaddedDescent_F_LenList
import Definitions.Def_PaddedDescent_F_Descend
import Theorems.Thm_Groundwork_BitCut_expand
import Theorems.Thm_Groundwork_PolyT_flatMap
import Theorems.Thm_Groundwork_PolyT_length
import Theorems.Thm_Groundwork_PolyT_map
import Theorems.Thm_Groundwork_PolyT_sum
attribute [local fun_prop] Groundwork.PolyT.flatMap
attribute [local fun_prop] Groundwork.PolyT.length
attribute [local fun_prop] Groundwork.PolyT.map
attribute [local fun_prop] Groundwork.PolyT.sum


set_option autoImplicit false
section
section
open PaddedDescent PaddedDescent.F
open Groundwork Groundwork.Prog Finset Lists
open Descend

theorem PaddedDescent.F.Descend.descend_list (h3 : StT3b) (hE : StE) {pad : U} : ∀ (sched : List Lvl) {Kup Λ B cnt : ℕ} (w : List PInst),
    Chain Kup sched → Fits pad.length Kup Λ B cnt sched → w.length ≤ cnt → (∀ I ∈ w, WF Kup Λ B I) →
    ((sched.foldl (fun w L => cap pad [] (w.flatMap (expand pad L))) w).map (bruteF pad 256)).sum = (w.map (zval Kup)).sum
  := by sorry
