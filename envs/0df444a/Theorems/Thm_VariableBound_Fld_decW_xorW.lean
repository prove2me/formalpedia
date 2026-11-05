-- Prove2me | Theorems.Thm_VariableBound_Fld_decW_xorW
-- name    : VariableBound.Fld.decW_xorW
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-04T17:39:29.065574+00:00
-- url     : https://prove2.me/theorems/bc2216e3-18c7-4aba-92fa-1fff5c8a297d
-- title:
--   Fld: dec W xor W
-- statement:
--   `xorW` is the sum of residues, for words of the same length.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/variables/VariableBound/Field/Search.lean#L30-L31
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/variables/VariableBound/Field/Search.lean#L30-L31

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

theorem VariableBound.Fld.decW_xorW (g : List Bool) {x y : List Bool} (h : x.length = y.length) : decW g (xorW x y) = decW g x + decW g y := by sorry
