-- Prove2me | Theorems.Thm_VariableBound_Fld_length_oneW
-- name    : VariableBound.Fld.length_oneW
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-04T16:52:45.990924+00:00
-- url     : https://prove2.me/theorems/5f1b2663-97e7-4178-b3f7-492a8dee3b43
-- title:
--   Fld: length one W
-- statement:
--   The word 1 is as long as g, if g is not empty.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/variables/VariableBound/Field/Ring.lean#L35-L36
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/variables/VariableBound/Field/Ring.lean#L35-L36

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

theorem VariableBound.Fld.length_oneW {g : List Bool} (hg : 1 ≤ g.length) : (oneW g).length = g.length := by sorry
