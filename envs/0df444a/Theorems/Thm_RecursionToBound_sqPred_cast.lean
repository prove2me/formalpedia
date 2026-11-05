-- Prove2me | Theorems.Thm_RecursionToBound_sqPred_cast
-- name    : RecursionToBound.sqPred_cast
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T02:15:39.578323+00:00
-- url     : https://prove2.me/theorems/e9dd60f6-714d-4585-bf44-aaeac298bf40
-- title:
--   Recursion To Bound: sq Pred cast
-- statement:
--   (k − 1)², computed in the rational numbers, is `sqPred k`.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/variables/RecursionToBound/Cert/Numbers.lean#L85-L93
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/variables/RecursionToBound/Cert/Numbers.lean#L85-L93

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

theorem RecursionToBound.sqPred_cast (k : ℕ) : ((k : ℚ) - 1) ^ 2 = ((sqPred k : ℕ) : ℚ) := by sorry
