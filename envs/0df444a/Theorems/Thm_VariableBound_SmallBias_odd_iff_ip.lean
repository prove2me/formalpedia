-- Prove2me | Theorems.Thm_VariableBound_SmallBias_odd_iff_ip
-- name    : VariableBound.SmallBias.odd_iff_ip
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-04T17:35:06.202463+00:00
-- url     : https://prove2.me/theorems/67fddf85-e3f7-47fa-9cad-f23fd1848b7b
-- title:
--   Small Bias: odd iff ip
-- statement:
--   For every set V′ of clauses and all u₃, u₄ ∈ 𝔽, the number of E ∈ V′ with ⟨u₃^ι(E), u₄⟩ = 1 is
--   odd if and only if ⟨w, u₄⟩ = 1, with w = Σ_{E ∈ V′} u₃^ι(E).
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/variables/VariableBound/Family/SmallBias.lean#L113-L115
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/variables/VariableBound/Family/SmallBias.lean#L113-L115

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

theorem VariableBound.SmallBias.odd_iff_ip (bits : F ≃ₗ[ZMod 2] (Fin s → ZMod 2)) (V' : Finset (Fin m)) (u₃ u₄ : F) :
    Odd #{E ∈ V' | ip (bits (u₃ ^ E.val)) (bits u₄) = 1} ↔ ip (bits (∑ E ∈ V', u₃ ^ E.val)) (bits u₄) = 1 := by sorry
