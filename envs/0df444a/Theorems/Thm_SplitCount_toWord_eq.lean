-- Prove2me | Theorems.Thm_SplitCount_toWord_eq
-- name    : SplitCount.toWord_eq
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T08:38:41.291705+00:00
-- url     : https://prove2.me/theorems/266ae29e-ca0b-4d97-b969-329e7241eee5
-- title:
--   Split Count: to Word eq
-- statement:
--   The ℓ-bit word of y lists the bits 0, …, ℓ − 1 of y.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/consequences/SplitCount/Sizes.lean#L89-L97
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/consequences/SplitCount/Sizes.lean#L89-L97

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_SplitCount_Defs
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Linarith
import Definitions.Def_SplitCount_Sizes
import Theorems.Thm_Groundwork_Decode_toWord_eq
import Theorems.Thm_Groundwork_PolyT_map
import Theorems.Thm_Groundwork_PolyT_testBit
attribute [local fun_prop] Groundwork.PolyT.map
attribute [local fun_prop] Groundwork.PolyT.testBit


set_option autoImplicit false
section
section
open SplitCount
open Groundwork Groundwork.Prog CountKSat

theorem SplitCount.toWord_eq (ℓ y : ℕ) : toWord ℓ y = (List.range ℓ).map y.testBit := by sorry
