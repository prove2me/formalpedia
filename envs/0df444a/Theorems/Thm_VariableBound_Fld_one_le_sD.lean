-- Prove2me | Theorems.Thm_VariableBound_Fld_one_le_sD
-- name    : VariableBound.Fld.one_le_sD
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-04T17:39:08.497959+00:00
-- url     : https://prove2.me/theorems/af9d99fc-1341-492a-ba95-0a16fc639dfd
-- title:
--   Fld: one le s D
-- statement:
--   s ≥ 1, for m ≥ 1.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/variables/VariableBound/Field/Transfer.lean#L140-L140
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/variables/VariableBound/Field/Transfer.lean#L140-L140

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

theorem VariableBound.Fld.one_le_sD {m : ℕ} (hm : 1 ≤ m) : 1 ≤ sD m := by sorry
