-- Prove2me | Theorems.Thm_VariableBound_Fld_decR_concat
-- name    : VariableBound.Fld.decR_concat
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-04T17:36:50.855929+00:00
-- url     : https://prove2.me/theorems/bd3a78ae-f2da-4260-8c00-fa62cceb2088
-- title:
--   Fld: dec R concat
-- statement:
--   A bit at the upper end of a word w of n bits adds that bit times r^n.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/variables/VariableBound/Field/Ring.lean#L94-L99
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/variables/VariableBound/Field/Ring.lean#L94-L99

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

theorem VariableBound.Fld.decR_concat (r : R) (w : List Bool) (b : Bool) : decR r (w ++ [b]) = decR r w + bitR R b * r ^ w.length := by sorry
