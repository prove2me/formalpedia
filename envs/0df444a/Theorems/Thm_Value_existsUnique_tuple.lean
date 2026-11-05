-- Prove2me | Theorems.Thm_Value_existsUnique_tuple
-- name    : Value.existsUnique_tuple
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T02:15:32.30904+00:00
-- url     : https://prove2.me/theorems/652705ff-fb89-4075-ad07-e7cef1ac869c
-- title:
--   Value: exists Unique tuple
-- statement:
--   Exactly one tuple has the entries t i at the indices i with P i.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/networks/Value/Words.lean#L36-L47
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/networks/Value/Words.lean#L36-L47

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_Value_Defs
import Definitions.Def_Value_Words
set_option autoImplicit false
section
section
open Value
open Groundwork Finset

theorem Value.existsUnique_tuple {ι X : Type*} [Fintype ι] [DecidableEq ι] (P : ι → Prop) [DecidablePred P] (T : ι → Finset X) (d : X) (t : ι → X) (ht : ∀ i, P i → t i ∈ T i) :
    ∃! b : ι → X, b ∈ tuples P T d ∧ ∀ i, P i → b i = t i := by sorry
