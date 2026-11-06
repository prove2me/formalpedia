-- Prove2me | Theorems.Thm_RecursionToBound_foldr_bind_max_of_some
-- name    : RecursionToBound.foldr_bind_max_of_some
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T03:54:31.897227+00:00
-- url     : https://prove2.me/theorems/2cb067ce-0c96-46f9-b891-0a46175b1ae3
-- title:
--   Recursion To Bound: foldr bind max of some
-- statement:
--   If every number is there, so is the maximum.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/variables/RecursionToBound/Cert/Numbers.lean#L151-L155
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/variables/RecursionToBound/Cert/Numbers.lean#L151-L155

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
import Theorems.Thm_Groundwork_PolyT_map
attribute [local fun_prop] Groundwork.PolyT.map


set_option autoImplicit false
section
section
open RecursionToBound
open Finset SparsificationLemma

theorem RecursionToBound.foldr_bind_max_of_some {f : ℕ → Option ℕ} {g : ℕ → ℕ} {l : List ℕ} (h : ∀ a ∈ l, f a = some (g a)) :
    l.foldr (fun a o => o.bind fun v => (f a).map (max v)) (some 0) = some ((l.map g).foldr max 0) := by sorry
