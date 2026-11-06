-- Prove2me | Theorems.Thm_RecursionToBound_exists_none_of_foldr_bind_max
-- name    : RecursionToBound.exists_none_of_foldr_bind_max
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T03:57:08.738502+00:00
-- url     : https://prove2.me/theorems/d431a356-189f-4f52-93e6-fb9166901740
-- title:
--   Recursion To Bound: exists none of foldr bind max
-- statement:
--   The maximum is missing only if one of the numbers is.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/variables/RecursionToBound/Cert/Numbers.lean#L158-L164
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/variables/RecursionToBound/Cert/Numbers.lean#L158-L164

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

theorem RecursionToBound.exists_none_of_foldr_bind_max {f : ℕ → Option ℕ} {l : List ℕ} (h : l.foldr (fun a o => o.bind fun v => (f a).map (max v)) (some 0) = none) :
    ∃ a ∈ l, f a = none := by sorry
