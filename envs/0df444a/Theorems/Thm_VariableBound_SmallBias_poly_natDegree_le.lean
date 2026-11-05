-- Prove2me | Theorems.Thm_VariableBound_SmallBias_poly_natDegree_le
-- name    : VariableBound.SmallBias.poly_natDegree_le
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-04T17:35:18.1685+00:00
-- url     : https://prove2.me/theorems/21b3a037-e11a-4a82-919b-006cabf5de3a
-- title:
--   Small Bias: poly nat Degree le
-- statement:
--   Proof of Lemma 13 (Family of checks), «of degree at most m − 1»: for every set V′ of clauses.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/variables/VariableBound/Family/SmallBias.lean#L151-L155
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/variables/VariableBound/Family/SmallBias.lean#L151-L155

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

theorem VariableBound.SmallBias.poly_natDegree_le (V' : Finset (Fin m)) : (poly F V').natDegree ≤ m - 1 := by sorry
