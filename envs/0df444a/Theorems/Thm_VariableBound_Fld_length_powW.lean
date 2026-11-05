-- Prove2me | Theorems.Thm_VariableBound_Fld_length_powW
-- name    : VariableBound.Fld.length_powW
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-04T16:52:49.870428+00:00
-- url     : https://prove2.me/theorems/bc43dedf-77c9-4691-afde-03cc513bfca1
-- title:
--   Fld: length pow W
-- statement:
--   u^e is as long as g, if g is not empty.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/variables/VariableBound/Field/Ring.lean#L59-L62
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/variables/VariableBound/Field/Ring.lean#L59-L62

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

theorem VariableBound.Fld.length_powW {g : List Bool} (hg : 1 ≤ g.length) (u : List Bool) (e : ℕ) : (powW g u e).length = g.length := by sorry
