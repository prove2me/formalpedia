-- Prove2me | Theorems.Thm_VariableBound_Fld_length_mulW
-- name    : VariableBound.Fld.length_mulW
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-04T16:50:36.36683+00:00
-- url     : https://prove2.me/theorems/0f82cd78-ebe5-4dcf-8190-51dd060de606
-- title:
--   Fld: length mul W
-- statement:
--   x·y is as long as g, if x is.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/variables/VariableBound/Field/Ring.lean#L44-L52
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/variables/VariableBound/Field/Ring.lean#L44-L52

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

theorem VariableBound.Fld.length_mulW {g x : List Bool} (hx : x.length = g.length) (y : List Bool) : (mulW g x y).length = g.length := by sorry
