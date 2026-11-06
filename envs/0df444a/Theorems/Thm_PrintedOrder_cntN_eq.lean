-- Prove2me | Theorems.Thm_PrintedOrder_cntN_eq
-- name    : PrintedOrder.cntN_eq
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T08:57:34.541071+00:00
-- url     : https://prove2.me/theorems/7384cd82-8771-461f-9498-f1284fba77d2
-- title:
--   Printed Order: cnt N eq
-- statement:
--   The number of satisfying assignments on n variables, written with `Holds`.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/consequences/PrintedOrder/AddUp.lean#L38-L40
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/consequences/PrintedOrder/AddUp.lean#L38-L40

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_PrintedOrder_Defs
import Definitions.Def_SplitCount_Disjoint
import Definitions.Def_SplitCount_Tree
import Definitions.Def_SparsificationLemma_One
import Mathlib.Tactic
import Definitions.Def_PrintedOrder_AddUp
import Theorems.Thm_Groundwork_PolyT_filter
attribute [local fun_prop] Groundwork.PolyT.filter


set_option autoImplicit false
section
section
open PrintedOrder
open Groundwork Groundwork.Prog Groundwork.Sparsify CountKSat SplitCount
open Classical

theorem PrintedOrder.cntN_eq (n : ℕ) (y : Fml) : cntN n y = (Finset.univ.filter fun b : Fin n → Bool => Holds (ext b) y).card := by sorry
