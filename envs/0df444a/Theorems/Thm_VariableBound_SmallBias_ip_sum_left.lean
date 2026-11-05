-- Prove2me | Theorems.Thm_VariableBound_SmallBias_ip_sum_left
-- name    : VariableBound.SmallBias.ip_sum_left
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-04T17:34:23.983203+00:00
-- url     : https://prove2.me/theorems/794d8099-2997-40d6-913a-d7f1fdfd114e
-- title:
--   Small Bias: ip sum left
-- statement:
--   ⟨Σ_e f e, y⟩ = Σ_e ⟨f e, y⟩.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/variables/VariableBound/Family/SmallBias.lean#L56-L58
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/variables/VariableBound/Family/SmallBias.lean#L56-L58

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

theorem VariableBound.SmallBias.ip_sum_left {ι : Type} (T : Finset ι) (f : ι → Fin s → ZMod 2) (y : Fin s → ZMod 2) : ip (∑ e ∈ T, f e) y = ∑ e ∈ T, ip (f e) y := by sorry
