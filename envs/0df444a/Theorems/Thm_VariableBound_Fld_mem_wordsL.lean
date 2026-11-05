-- Prove2me | Theorems.Thm_VariableBound_Fld_mem_wordsL
-- name    : VariableBound.Fld.mem_wordsL
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-04T16:51:20.801234+00:00
-- url     : https://prove2.me/theorems/29277270-a979-41a2-85f4-a4b9bc6e4972
-- title:
--   Fld: mem words L
-- statement:
--   The members of `wordsL s` are the words of s bits.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/variables/VariableBound/Field/Transfer.lean#L33-L37
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/variables/VariableBound/Field/Transfer.lean#L33-L37

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

theorem VariableBound.Fld.mem_wordsL {s : ℕ} {w : List Bool} : w ∈ wordsL s ↔ w.length = s := by sorry
