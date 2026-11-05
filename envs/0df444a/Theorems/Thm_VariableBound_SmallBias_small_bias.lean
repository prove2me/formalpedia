-- Prove2me | Theorems.Thm_VariableBound_SmallBias_small_bias
-- name    : VariableBound.SmallBias.small_bias
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-04T17:35:44.410756+00:00
-- url     : https://prove2.me/theorems/20417eee-ecbb-477a-9e7c-407b12fa72ed
-- title:
--   Small Bias: small bias
-- statement:
--   Proof of Lemma 13 (Family of checks), the small-bias parity: if 16m ≤ 2^s, then for every
--   nonempty set V′ of clauses, Σ_{E ∈ V′} ⟨u₃^ι(E), u₄⟩ is odd with probability at least 15/32 over
--   (u₃, u₄) ∈ 𝔽².
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/variables/VariableBound/Family/SmallBias.lean#L226-L233
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/variables/VariableBound/Family/SmallBias.lean#L226-L233

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
variable {F : Type} [Field F] [Fintype F] [Algebra (ZMod 2) F] {m s : ℕ}

theorem VariableBound.SmallBias.small_bias (bits : F ≃ₗ[ZMod 2] (Fin s → ZMod 2)) (h16 : 16 * m ≤ 2 ^ s) (V' : Finset (Fin m)) (hV : V'.Nonempty) :
    15 * Fintype.card F ^ 2 ≤ 32 * #{p : F × F | Odd #{E ∈ V' | ip (bits (p.1 ^ E.val)) (bits p.2) = 1}} := by sorry
