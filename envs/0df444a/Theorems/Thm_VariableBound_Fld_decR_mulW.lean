-- Prove2me | Theorems.Thm_VariableBound_Fld_decR_mulW
-- name    : VariableBound.Fld.decR_mulW
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-04T16:52:58.869913+00:00
-- url     : https://prove2.me/theorems/5c3f9f7f-1113-48f7-9afe-1fccf52b25e9
-- title:
--   Fld: dec R mul W
-- statement:
--   In a ring with 2 = 0 and for r^s = `decR r g` (r a root of X^s + g), `mulW g` is the product,
--   for a word x of s bits, s the length of g, and any word y.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/variables/VariableBound/Field/Ring.lean#L120-L132
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/variables/VariableBound/Field/Ring.lean#L120-L132

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

theorem VariableBound.Fld.decR_mulW (h2 : (2 : R) = 0) {r : R} {g : List Bool} (hr : r ^ g.length = decR r g) {x : List Bool} (hx : x.length = g.length) (y : List Bool) :
    decR r (mulW g x y) = decR r x * decR r y := by sorry
