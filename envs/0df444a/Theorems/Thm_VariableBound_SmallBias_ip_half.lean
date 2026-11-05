-- Prove2me | Theorems.Thm_VariableBound_SmallBias_ip_half
-- name    : VariableBound.SmallBias.ip_half
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-04T16:08:44.105894+00:00
-- url     : https://prove2.me/theorems/9e894820-f232-4616-be8d-b2e33d9c92ba
-- title:
--   Small Bias: ip half
-- statement:
--   Proof of Lemma 13 (Family of checks), «for w ≠ 0 the probability is 1/2»: for w ∈ 𝔽, w ≠ 0,
--   exactly half of the u₄ ∈ 𝔽 have ⟨w, u₄⟩ = 1.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/variables/VariableBound/Family/SmallBias.lean#L178-L182
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/variables/VariableBound/Family/SmallBias.lean#L178-L182

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
variable {F : Type} [Field F] [Fintype F] [Algebra (ZMod 2) F] {s : ℕ}

theorem VariableBound.SmallBias.ip_half (bits : F ≃ₗ[ZMod 2] (Fin s → ZMod 2)) (w : F) (hw : w ≠ 0) : 2 * #{u₄ : F | ip (bits w) (bits u₄) = 1} = Fintype.card F := by sorry
