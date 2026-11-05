-- Prove2me | Theorems.Thm_VariableBound_SmallBias_poly_ne_zero
-- name    : VariableBound.SmallBias.poly_ne_zero
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-04T17:35:17.867251+00:00
-- url     : https://prove2.me/theorems/492a8e69-d5c3-4e93-8f9d-48fa2baa5586
-- title:
--   Small Bias: poly ne zero
-- statement:
--   Proof of Lemma 13 (Family of checks), «a nonzero polynomial»: for V′ nonempty; the coefficient
--   of X^ι(E) is 1 for E ∈ V′, because ι is injective.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/variables/VariableBound/Family/SmallBias.lean#L135-L148
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/variables/VariableBound/Family/SmallBias.lean#L135-L148

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
variable {F : Type} [Field F] {m : ℕ}

theorem VariableBound.SmallBias.poly_ne_zero (V' : Finset (Fin m)) (hV : V'.Nonempty) : poly F V' ≠ 0 := by sorry
