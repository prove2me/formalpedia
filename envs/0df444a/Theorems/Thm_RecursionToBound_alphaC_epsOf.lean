-- Prove2me | Theorems.Thm_RecursionToBound_alphaC_epsOf
-- name    : RecursionToBound.alphaC_epsOf
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-05T03:54:18.608614+00:00
-- url     : https://prove2.me/theorems/ca3618ea-a176-4951-9c27-7405dd5a3efb
-- title:
--   Recursion To Bound: alpha C eps Of
-- statement:
--   **α of the thresholds, without fractions**: `Cal.alphaC k (epsOf r)` = ⌈2·(k−1)²·b·L / min(a,
--   b)⌉, for all k and r = (a, b).
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/variables/RecursionToBound/Cert/Numbers.lean#L102-L104
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/variables/RecursionToBound/Cert/Numbers.lean#L102-L104

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

theorem RecursionToBound.alphaC_epsOf (k : ℕ) (r : ℕ × ℕ) : Cal.alphaC k (epsOf r) = alphaN k r := by sorry
