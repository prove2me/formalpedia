-- Prove2me | Theorems.Thm_VariableBound_SmallBias_half
-- name    : VariableBound.SmallBias.half
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-04T17:35:47.567878+00:00
-- url     : https://prove2.me/theorems/fd1feaec-d046-46a6-a026-177d09c5a13f
-- title:
--   Small Bias: half
-- statement:
--   Proof of Lemma 13 (Family of checks), the half of «a clause lies in Γ_u with probability at most
--   1/v» on (u₃, u₄): for every clause E, ⟨u₃^ι(E), u₄⟩ = 1 with probability at most 1/2 over (u₃, u₄) ∈
--   𝔽².
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/variables/VariableBound/Family/SmallBias.lean#L238-L242
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/variables/VariableBound/Family/SmallBias.lean#L238-L242

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

theorem VariableBound.SmallBias.half (bits : F ≃ₗ[ZMod 2] (Fin s → ZMod 2)) (E : Fin m) :
    2 * #{p : F × F | ip (bits (p.1 ^ E.val)) (bits p.2) = 1} ≤ Fintype.card F ^ 2 := by sorry
