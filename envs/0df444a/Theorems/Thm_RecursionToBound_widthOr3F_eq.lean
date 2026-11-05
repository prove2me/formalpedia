-- Prove2me | Theorems.Thm_RecursionToBound_widthOr3F_eq
-- name    : RecursionToBound.widthOr3F_eq
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-05T03:57:08.312192+00:00
-- url     : https://prove2.me/theorems/9169ebea-9247-4139-802c-419be0bdc1cb
-- title:
--   Recursion To Bound: width Or3 F eq
-- statement:
--   The width of Step 5 as the maximum of a list.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/variables/RecursionToBound/Cert/Numbers.lean#L134-L135
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/variables/RecursionToBound/Cert/Numbers.lean#L134-L135

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
import Theorems.Thm_Groundwork_PolyT_length
import Theorems.Thm_Groundwork_PolyT_map
attribute [local fun_prop] Groundwork.PolyT.length
attribute [local fun_prop] Groundwork.PolyT.map


set_option autoImplicit false
section
section
open RecursionToBound
open Finset SparsificationLemma

theorem RecursionToBound.widthOr3F_eq (ψ : Groundwork.Prog.Fml) : widthOr3F ψ = max 3 ((ψ.map List.length).foldr max 0) := by sorry
