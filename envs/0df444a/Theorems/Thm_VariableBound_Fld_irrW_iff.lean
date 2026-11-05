-- Prove2me | Theorems.Thm_VariableBound_Fld_irrW_iff
-- name    : VariableBound.Fld.irrW_iff
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-04T17:39:58.68218+00:00
-- url     : https://prove2.me/theorems/94334dcc-a8da-46af-8590-4a32e7bac156
-- title:
--   Fld: irr W iff
-- statement:
--   For a word g of s ≥ 1 bits, the test holds exactly if X^s + g is irreducible.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/variables/VariableBound/Field/Search.lean#L56-L73
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/variables/VariableBound/Field/Search.lean#L56-L73

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

theorem VariableBound.Fld.irrW_iff {g : List Bool} (hg : 1 ≤ g.length) : irrW g = true ↔ Irreducible (modP g) := by sorry
