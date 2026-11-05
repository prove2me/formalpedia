-- Prove2me | Theorems.Thm_P2M_ExplicitCost_size_unary__02a080207638
-- name    : P2M_ExplicitCost_size_unary__02a080207638
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T05:49:51.149706+00:00
-- url     : https://prove2.me/theorems/d9dcf608-540c-486d-ae19-e8c80ce5eeb3
-- title:
--   P2 M Explicit Cost size unary  02a080207638: P2 M Explicit Cost size unary  02a080207638
-- statement:
--   The size of a number in unary.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/CountedRecursion/Numbers.lean#L32-L37
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/CountedRecursion/Numbers.lean#L32-L37

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_CountedRecursion_AnswersDefs
import Definitions.Def_ToTuring_Poly_Range
import Definitions.Def_ToTuring_Poly_Comb
import Definitions.Def_ToTuring_Lib_Unary
import Mathlib.Tactic
import Definitions.Def_CountedRecursion_Numbers
set_option autoImplicit false
section
section
open ExplicitCost
open Groundwork QueryMachines Printed

theorem P2M_ExplicitCost_size_unary__02a080207638 (n : ℕ) : size (unary n) = 2 * n + 1 := by sorry

alias «ExplicitCost».«size_unary'» := P2M_ExplicitCost_size_unary__02a080207638
