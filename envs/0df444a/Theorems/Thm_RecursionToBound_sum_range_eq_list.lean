-- Prove2me | Theorems.Thm_RecursionToBound_sum_range_eq_list
-- name    : RecursionToBound.sum_range_eq_list
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T03:56:38.404074+00:00
-- url     : https://prove2.me/theorems/b91814c2-f1ea-4831-905f-1ae1436d5711
-- title:
--   Recursion To Bound: sum range eq list
-- statement:
--   A sum over the numbers below k is the sum of a list.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/variables/RecursionToBound/Cert/Numbers.lean#L114-L117
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/variables/RecursionToBound/Cert/Numbers.lean#L114-L117

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
import Theorems.Thm_ClauseBound_Boson_Dual_sum_range_eq_list
import Theorems.Thm_Groundwork_PolyT_map
import Theorems.Thm_Groundwork_PolyT_sum
attribute [local fun_prop] Groundwork.PolyT.map
attribute [local fun_prop] Groundwork.PolyT.sum


set_option autoImplicit false
section
section
open RecursionToBound
open Finset SparsificationLemma

theorem RecursionToBound.sum_range_eq_list (f : ℕ → ℕ) (k : ℕ) : ∑ j ∈ range k, f j = ((List.range k).map f).sum := by sorry
