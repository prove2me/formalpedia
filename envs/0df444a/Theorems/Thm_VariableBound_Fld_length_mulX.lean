-- Prove2me | Theorems.Thm_VariableBound_Fld_length_mulX
-- name    : VariableBound.Fld.length_mulX
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-04T16:52:47.807198+00:00
-- url     : https://prove2.me/theorems/7bf2c5d3-93e7-4181-a980-b7054c194db7
-- title:
--   Fld: length mul X
-- statement:
--   X·w is as long as g, if w is.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/variables/VariableBound/Field/Ring.lean#L39-L41
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/variables/VariableBound/Field/Ring.lean#L39-L41

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

theorem VariableBound.Fld.length_mulX {g w : List Bool} (hw : w.length = g.length) : (mulX g w).length = g.length := by sorry
