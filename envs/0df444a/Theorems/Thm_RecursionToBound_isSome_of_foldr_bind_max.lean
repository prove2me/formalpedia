-- Prove2me | Theorems.Thm_RecursionToBound_isSome_of_foldr_bind_max
-- name    : RecursionToBound.isSome_of_foldr_bind_max
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-05T03:56:39.696529+00:00
-- url     : https://prove2.me/theorems/ebec7093-f8b1-45fa-af93-e729c08634a3
-- title:
--   Recursion To Bound: is Some of foldr bind max
-- statement:
--   If the maximum is there, so is every number.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/variables/RecursionToBound/Cert/Numbers.lean#L167-L171
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/variables/RecursionToBound/Cert/Numbers.lean#L167-L171

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

theorem RecursionToBound.isSome_of_foldr_bind_max {f : ℕ → Option ℕ} {l : List ℕ} {v : ℕ} (h : l.foldr (fun a o => o.bind fun v => (f a).map (max v)) (some 0) = some v) :
    ∀ a ∈ l, (f a).isSome = true := by sorry
