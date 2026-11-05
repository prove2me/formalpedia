-- Prove2me | Theorems.Thm_VariableBound_SmallBias_sum_ip
-- name    : VariableBound.SmallBias.sum_ip
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-04T17:35:03.640891+00:00
-- url     : https://prove2.me/theorems/478ab7d9-d55f-40f8-9b62-d0d406fe62d5
-- title:
--   Small Bias: sum ip
-- statement:
--   Proof of Lemma 13 (Family of checks), «the sum is ⟨w, u₄⟩ modulo 2 with w = Σ_{E ∈ V′} u₃^ι(E)»:
--   for every set V′ of clauses and all u₃, u₄ ∈ 𝔽.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/variables/VariableBound/Family/SmallBias.lean#L107-L109
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/variables/VariableBound/Family/SmallBias.lean#L107-L109

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
variable {F : Type} [Field F] [Algebra (ZMod 2) F] {m s : ℕ}

theorem VariableBound.SmallBias.sum_ip (bits : F ≃ₗ[ZMod 2] (Fin s → ZMod 2)) (V' : Finset (Fin m)) (u₃ u₄ : F) :
    ∑ E ∈ V', ip (bits (u₃ ^ E.val)) (bits u₄) = ip (bits (∑ E ∈ V', u₃ ^ E.val)) (bits u₄) := by sorry
