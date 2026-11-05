-- Prove2me | Theorems.Thm_VariableBound_SmallBias_roots
-- name    : VariableBound.SmallBias.roots
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-04T17:35:14.051038+00:00
-- url     : https://prove2.me/theorems/80a04f81-2fa9-4071-8aa2-5961fc456755
-- title:
--   Small Bias: roots
-- statement:
--   Proof of Lemma 13 (Family of checks), «so w = 0 for at most m − 1 values of u₃»: for V′
--   nonempty.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/variables/VariableBound/Family/SmallBias.lean#L159-L162
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/variables/VariableBound/Family/SmallBias.lean#L159-L162

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

theorem VariableBound.SmallBias.roots [Fintype F] [DecidableEq F] (V' : Finset (Fin m)) (hV : V'.Nonempty) : #{u₃ : F | ∑ E ∈ V', u₃ ^ E.val = 0} ≤ m - 1 := by sorry
