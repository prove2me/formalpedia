-- Prove2me | Theorems.Thm_Value_existsUnique_pi
-- name    : Value.existsUnique_pi
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T02:15:54.050199+00:00
-- url     : https://prove2.me/theorems/debe8763-fb58-43e7-9663-f62675453351
-- title:
--   Value: exists Unique pi
-- statement:
--   If at every index exactly one x is right, then exactly one family is right at every index.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/networks/Value/Words.lean#L32-L33
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/networks/Value/Words.lean#L32-L33

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

theorem Value.existsUnique_pi {ι X : Type*} (R : ι → X → Prop) (h : ∀ i, ∃! x, R i x) : ∃! f : ι → X, ∀ i, R i (f i) := by sorry
