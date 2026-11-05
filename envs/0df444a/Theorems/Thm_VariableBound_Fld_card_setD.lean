-- Prove2me | Theorems.Thm_VariableBound_Fld_card_setD
-- name    : VariableBound.Fld.card_setD
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-04T17:38:21.178832+00:00
-- url     : https://prove2.me/theorems/7a31819d-2a30-4bb6-9d58-ba5a21d2fe29
-- title:
--   Fld: card set D
-- statement:
--   A list of numbers below m without repetitions has as many members as the set it lists.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/variables/VariableBound/Field/Transfer.lean#L68-L73
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/variables/VariableBound/Field/Transfer.lean#L68-L73

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

theorem VariableBound.Fld.card_setD {m : ℕ} {l : List ℕ} (h1 : l.Nodup) (h2 : ∀ E ∈ l, E < m) : #(setD m l) = l.length := by sorry
