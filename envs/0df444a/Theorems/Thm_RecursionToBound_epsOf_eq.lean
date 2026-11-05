-- Prove2me | Theorems.Thm_RecursionToBound_epsOf_eq
-- name    : RecursionToBound.epsOf_eq
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T01:00:01.359331+00:00
-- url     : https://prove2.me/theorems/e119eaf3-f3ba-42ff-ae2f-8f602194eb47
-- title:
--   Recursion To Bound: eps Of eq
-- statement:
--   ε = min(a/b, 1) = min(a, b)/b, for all a and b.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/variables/RecursionToBound/Cert/Numbers.lean#L78-L82
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/variables/RecursionToBound/Cert/Numbers.lean#L78-L82

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

theorem RecursionToBound.epsOf_eq (r : ℕ × ℕ) : epsOf r = ((min r.1 r.2 : ℕ) : ℚ) / (r.2 : ℚ) := by sorry
