-- Prove2me | Theorems.Thm_P2M_ExplicitCost_length_unary__ce48a98cee10
-- name    : P2M_ExplicitCost_length_unary__ce48a98cee10
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-05T05:50:00.73984+00:00
-- url     : https://prove2.me/theorems/5b56a38a-f20f-45f2-92ee-f9eb327c07f8
-- title:
--   P2 M Explicit Cost length unary  ce48a98cee10: P2 M Explicit Cost length unary  ce48a98cee10
-- statement:
--   The length of a number in unary.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/CountedRecursion/Numbers.lean#L29-L29
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/CountedRecursion/Numbers.lean#L29-L29

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_CountedRecursion_AnswersDefs
import Definitions.Def_ToTuring_Poly_Range
import Definitions.Def_ToTuring_Poly_Comb
import Definitions.Def_ToTuring_Lib_Unary
import Mathlib.Tactic
import Definitions.Def_CountedRecursion_Numbers
import Theorems.Thm_Groundwork_PolyT_length
attribute [local fun_prop] Groundwork.PolyT.length


set_option autoImplicit false
section
section
open ExplicitCost
open Groundwork QueryMachines Printed

theorem P2M_ExplicitCost_length_unary__ce48a98cee10 (n : ℕ) : (unary n).length = n := by sorry

alias «ExplicitCost».«length_unary'» := P2M_ExplicitCost_length_unary__ce48a98cee10
