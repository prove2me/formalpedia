-- Prove2me | Theorems.Thm_VariableBound_SmallBias_odd_iff
-- name    : VariableBound.SmallBias.odd_iff
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-04T17:35:04.474637+00:00
-- url     : https://prove2.me/theorems/29c7c900-ea0d-4f4a-bddc-83d88b242038
-- title:
--   Small Bias: odd iff
-- statement:
--   For f with values in ZMod 2, the number of e ∈ T with f e = 1 is odd if and only if the sum of
--   the f e over e ∈ T is 1.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/variables/VariableBound/Family/SmallBias.lean#L88-L91
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/variables/VariableBound/Family/SmallBias.lean#L88-L91

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

theorem VariableBound.SmallBias.odd_iff {ι : Type} (T : Finset ι) (f : ι → ZMod 2) : Odd #{e ∈ T | f e = 1} ↔ ∑ e ∈ T, f e = 1 := by sorry
