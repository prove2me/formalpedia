-- Prove2me | Theorems.Thm_RecursionToBound_ceil_natCast_div
-- name    : RecursionToBound.ceil_natCast_div
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T00:58:56.6952+00:00
-- url     : https://prove2.me/theorems/82b22b2e-800b-40af-99f6-ac39c53d7313
-- title:
--   Recursion To Bound: ceil nat Cast div
-- statement:
--   The ceiling of a quotient of natural numbers, for all m and p.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/variables/RecursionToBound/Cert/Numbers.lean#L57-L75
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/variables/RecursionToBound/Cert/Numbers.lean#L57-L75

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
set_option autoImplicit false
section
section
open RecursionToBound
open Finset SparsificationLemma

theorem RecursionToBound.ceil_natCast_div (m p : ℕ) : ⌈(m : ℚ) / (p : ℚ)⌉₊ = ceilDiv m p := by sorry
