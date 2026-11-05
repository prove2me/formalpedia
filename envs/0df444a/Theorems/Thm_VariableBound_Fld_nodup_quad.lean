-- Prove2me | Theorems.Thm_VariableBound_Fld_nodup_quad
-- name    : VariableBound.Fld.nodup_quad
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-04T17:38:04.744248+00:00
-- url     : https://prove2.me/theorems/d517cc88-6df9-4350-8fd0-309019e0188e
-- title:
--   Fld: nodup quad
-- statement:
--   No quadruple occurs twice in the four-fold product.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/variables/VariableBound/Field/Transfer.lean#L50-L51
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/variables/VariableBound/Field/Transfer.lean#L50-L51

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

theorem VariableBound.Fld.nodup_quad (s : ℕ) : (wordsL s ×ˢ wordsL s ×ˢ wordsL s ×ˢ wordsL s).Nodup := by sorry
