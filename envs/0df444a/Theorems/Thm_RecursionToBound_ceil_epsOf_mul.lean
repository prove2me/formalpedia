-- Prove2me | Theorems.Thm_RecursionToBound_ceil_epsOf_mul
-- name    : RecursionToBound.ceil_epsOf_mul
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-05T03:54:22.587198+00:00
-- url     : https://prove2.me/theorems/bffa138a-ea93-4f5c-9596-74482d653331
-- title:
--   Recursion To Bound: ceil eps Of mul
-- statement:
--   **⌈ε·n⌉ without fractions**: ⌈min(a, b)·n / b⌉, for all r = (a, b) and n.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/variables/RecursionToBound/Cert/Numbers.lean#L107-L109
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/variables/RecursionToBound/Cert/Numbers.lean#L107-L109

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

theorem RecursionToBound.ceil_epsOf_mul (r : ℕ × ℕ) (n : ℕ) : ⌈epsOf r * (n : ℚ)⌉₊ = ceilDiv (min r.1 r.2 * n) r.2 := by sorry
