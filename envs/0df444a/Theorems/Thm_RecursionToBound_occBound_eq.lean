-- Prove2me | Theorems.Thm_RecursionToBound_occBound_eq
-- name    : RecursionToBound.occBound_eq
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T04:00:42.34255+00:00
-- url     : https://prove2.me/theorems/ff088e72-a3d8-4115-ad88-cd15395b2989
-- title:
--   Recursion To Bound: occ Bound eq
-- statement:
--   The bound on the occurrences as the sum of a list.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/variables/RecursionToBound/Cert/Numbers.lean#L120-L121
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/variables/RecursionToBound/Cert/Numbers.lean#L120-L121

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
import Theorems.Thm_Groundwork_PolyT_sum
attribute [local fun_prop] Groundwork.PolyT.map
attribute [local fun_prop] Groundwork.PolyT.sum


set_option autoImplicit false
section
section
open RecursionToBound
open Finset SparsificationLemma

theorem RecursionToBound.occBound_eq (k : ℕ) (r : ℕ × ℕ) : occBound k r = 2 * ((List.range k).map (thresholds k r)).sum + 2 := by sorry
