-- Prove2me | Theorems.Thm_VariableBound_SmallBias_ip_add_right
-- name    : VariableBound.SmallBias.ip_add_right
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-04T17:32:47.470207+00:00
-- url     : https://prove2.me/theorems/3b73031b-de47-47a4-9efa-0d72b20c6bc8
-- title:
--   Small Bias: ip add right
-- statement:
--   ⟨x, y + z⟩ = ⟨x, y⟩ + ⟨x, z⟩.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/variables/VariableBound/Family/SmallBias.lean#L52-L53
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/variables/VariableBound/Family/SmallBias.lean#L52-L53

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_AppVariablesStatement
import Mathlib.Algebra.Polynomial.Eval.Defs
import Mathlib.Algebra.Polynomial.Degree.Defs
import Mathlib.Algebra.Polynomial.Roots
import Mathlib.Algebra.Polynomial.BigOperators
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Data.ZMod.Basic
import Definitions.Def_VariableBound_Family_SmallBias
set_option autoImplicit false
section
section
open VariableBound VariableBound.SmallBias
open Finset AppVariables
variable {s : ℕ}

theorem VariableBound.SmallBias.ip_add_right (x y z : Fin s → ZMod 2) : ip x (y + z) = ip x y + ip x z := by sorry
