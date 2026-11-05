-- Prove2me | Theorems.Thm_VariableBound_Fld_nodup_wordsL
-- name    : VariableBound.Fld.nodup_wordsL
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-04T17:38:01.363894+00:00
-- url     : https://prove2.me/theorems/96e11ce2-bbbe-43d6-800e-ddccbe330bdd
-- title:
--   Fld: nodup words L
-- statement:
--   No word occurs twice in `wordsL s`.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/variables/VariableBound/Field/Transfer.lean#L40-L41
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/variables/VariableBound/Field/Transfer.lean#L40-L41

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

theorem VariableBound.Fld.nodup_wordsL (s : ℕ) : (wordsL s).Nodup := by sorry
