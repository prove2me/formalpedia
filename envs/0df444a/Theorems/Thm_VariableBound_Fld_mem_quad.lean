-- Prove2me | Theorems.Thm_VariableBound_Fld_mem_quad
-- name    : VariableBound.Fld.mem_quad
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-04T16:51:25.341032+00:00
-- url     : https://prove2.me/theorems/f55a64a0-c131-43d7-8c5e-bec621437f4b
-- title:
--   Fld: mem quad
-- statement:
--   The members of the four-fold product are the quadruples of words of s bits.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/variables/VariableBound/Field/Transfer.lean#L44-L47
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/variables/VariableBound/Field/Transfer.lean#L44-L47

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_VariableBound_Field_Defs
import Mathlib.Data.List.ProdSigma
import Mathlib.Data.List.Nodup
import Mathlib.Data.Finset.Image
import Mathlib.Data.Fintype.Card
import Mathlib.Data.Nat.Log
import Definitions.Def_VariableBound_Field_Transfer
set_option autoImplicit false
section
section
open VariableBound VariableBound.Fld
open Groundwork Finset

theorem VariableBound.Fld.mem_quad {s : ℕ} {u : List Bool × List Bool × List Bool × List Bool} :
    u ∈ wordsL s ×ˢ wordsL s ×ˢ wordsL s ×ˢ wordsL s ↔ u.1.length = s ∧ u.2.1.length = s ∧ u.2.2.1.length = s ∧ u.2.2.2.length = s := by sorry
