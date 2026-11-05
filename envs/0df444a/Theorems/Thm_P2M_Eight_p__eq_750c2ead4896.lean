-- Prove2me | Theorems.Thm_P2M_Eight_p__eq_750c2ead4896
-- name    : P2M_Eight_p__eq_750c2ead4896
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-04T16:40:30.419192+00:00
-- url     : https://prove2.me/theorems/12f8e522-810c-40a5-8710-e95364388edf
-- title:
--   P2 M Eight p  eq 750c2ead4896: P2 M Eight p  eq 750c2ead4896
-- statement:
--   «So p' = p ⊕ d».
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/networks/Eight/SecCrossing_Identity.lean#L76-L77
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/networks/Eight/SecCrossing_Identity.lean#L76-L77

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_EightSquareStatement
import Mathlib.Data.Nat.ModEq
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring
import Definitions.Def_Eight_SecCrossing_Identity
set_option autoImplicit false
section
section
open Eight
open Finset

theorem P2M_Eight_p__eq_750c2ead4896 {p q p' q' : Block} (h : bxor p q = bxor p' q') : p' = bxor p (bxor q q') := by sorry

alias «Eight».«p'_eq» := P2M_Eight_p__eq_750c2ead4896
