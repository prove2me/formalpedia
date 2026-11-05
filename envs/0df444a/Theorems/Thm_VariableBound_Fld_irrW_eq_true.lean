-- Prove2me | Theorems.Thm_VariableBound_Fld_irrW_eq_true
-- name    : VariableBound.Fld.irrW_eq_true
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-04T17:39:51.223947+00:00
-- url     : https://prove2.me/theorems/a1c5edd1-4ced-44e3-bc92-5e0986341536
-- title:
--   Fld: irr W eq true
-- statement:
--   What the test says: every word x as long as g is the word 0 or has a word y as long as g with
--   x·y = 1.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/variables/VariableBound/Field/Search.lean#L51-L53
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/variables/VariableBound/Field/Search.lean#L51-L53

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

theorem VariableBound.Fld.irrW_eq_true {g : List Bool} : irrW g = true ↔
    ∀ x : List Bool, x.length = g.length → x = zeroW g ∨ ∃ y : List Bool, y.length = g.length ∧ mulW g x y = oneW g := by sorry
