-- Prove2me | Theorems.Thm_VariableBound_Fld_length_xorW
-- name    : VariableBound.Fld.length_xorW
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-04T16:51:06.212772+00:00
-- url     : https://prove2.me/theorems/6d27a35c-4863-47a1-9d68-777e46ef3e63
-- title:
--   Fld: length xor W
-- statement:
--   The sum is as long as the shorter word.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/variables/VariableBound/Field/Ring.lean#L29-L29
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/variables/VariableBound/Field/Ring.lean#L29-L29

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_VariableBound_Field_Alg
import Mathlib.Tactic.Ring
import Mathlib.Tactic.LinearCombination
import Definitions.Def_VariableBound_Field_Ring
set_option autoImplicit false
section
section
open VariableBound VariableBound.Fld
variable {R : Type} [CommRing R]

theorem VariableBound.Fld.length_xorW (x y : List Bool) : (xorW x y).length = min x.length y.length := by sorry
