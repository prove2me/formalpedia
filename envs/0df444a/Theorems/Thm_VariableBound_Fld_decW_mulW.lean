-- Prove2me | Theorems.Thm_VariableBound_Fld_decW_mulW
-- name    : VariableBound.Fld.decW_mulW
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-04T16:53:41.090505+00:00
-- url     : https://prove2.me/theorems/a097120c-4626-4115-adfa-856289ea98db
-- title:
--   Fld: dec W mul W
-- statement:
--   `mulW g` is the product of residues, for a word x as long as g and any word y.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/variables/VariableBound/Field/Search.lean#L40-L41
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/variables/VariableBound/Field/Search.lean#L40-L41

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_VariableBound_Field_Ring
import Definitions.Def_VariableBound_Field_Quot
import Definitions.Def_VariableBound_Field_Transfer
import Definitions.Def_VariableBound_Field_Search
set_option autoImplicit false
section
section
open VariableBound VariableBound.Fld
open Polynomial

theorem VariableBound.Fld.decW_mulW (g : List Bool) {x : List Bool} (hx : x.length = g.length) (y : List Bool) : decW g (mulW g x y) = decW g x * decW g y := by sorry
