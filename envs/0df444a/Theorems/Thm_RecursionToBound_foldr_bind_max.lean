-- Prove2me | Theorems.Thm_RecursionToBound_foldr_bind_max
-- name    : RecursionToBound.foldr_bind_max
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T00:21:47.917137+00:00
-- url     : https://prove2.me/theorems/5c3babb7-116b-4ebb-9989-e3c9bc42cc4f
-- title:
--   Recursion To Bound: foldr bind max
-- statement:
--   The maximum computed from the right, where every number may be missing: it is missing if one of
--   the numbers is, and else it is the maximum of the list.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/variables/RecursionToBound/Cert/Numbers.lean#L141-L148
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/variables/RecursionToBound/Cert/Numbers.lean#L141-L148

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_RecursionToBound_Defs
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring
import Mathlib.Tactic.SplitIfs
import Mathlib.Tactic.ByContra
import Definitions.Def_RecursionToBound_Cert_Numbers
import Theorems.Thm_Groundwork_PolyT_all
import Theorems.Thm_Groundwork_PolyT_map
attribute [local fun_prop] Groundwork.PolyT.all
attribute [local fun_prop] Groundwork.PolyT.map


set_option autoImplicit false
section
section
open RecursionToBound
open Finset SparsificationLemma

theorem RecursionToBound.foldr_bind_max (f : ℕ → Option ℕ) (l : List ℕ) :
    l.foldr (fun a o => o.bind fun v => (f a).map (max v)) (some 0) =
      if l.all (fun a => (f a).isSome) then some ((l.map fun a => (f a).getD 0).foldr max 0) else none := by sorry
