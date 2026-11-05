-- Prove2me | Theorems.Thm_VariableBound_SmallBias_small_bias_count
-- name    : VariableBound.SmallBias.small_bias_count
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-04T17:35:37.283121+00:00
-- url     : https://prove2.me/theorems/873746d6-52e1-4e7c-bcdd-179dfa54a184
-- title:
--   Small Bias: small bias count
-- statement:
--   Proof of Lemma 13 (Family of checks), «for every nonempty set V′ of clauses, Σ_{E ∈ V′}
--   ⟨u₃^ι(E), u₄⟩ is odd with probability at least (1/2)·(1 − (m−1)/2^s)» over (u₃, u₄) ∈ 𝔽²: multiplied
--   by 2·|𝔽|², where |𝔽| = 2^s,
--   this is |𝔽|² ≤ 2·(number of pairs) + (m−1)·|𝔽|. As V′ is nonempty, m ≥ 1.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/variables/VariableBound/Family/SmallBias.lean#L207-L221
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/variables/VariableBound/Family/SmallBias.lean#L207-L221

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

theorem VariableBound.SmallBias.small_bias_count (bits : F ≃ₗ[ZMod 2] (Fin s → ZMod 2)) (V' : Finset (Fin m)) (hV : V'.Nonempty) :
    Fintype.card F ^ 2 ≤ 2 * #{p : F × F | Odd #{E ∈ V' | ip (bits (p.1 ^ E.val)) (bits p.2) = 1}} + (m - 1) * Fintype.card F := by sorry
