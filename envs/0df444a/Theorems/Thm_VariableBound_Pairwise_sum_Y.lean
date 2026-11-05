-- Prove2me | Theorems.Thm_VariableBound_Pairwise_sum_Y
-- name    : VariableBound.Pairwise.sum_Y
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-04T17:32:01.317208+00:00
-- url     : https://prove2.me/theorems/40dac0c8-8314-44ef-9e39-f4aad436943b
-- title:
--   Pairwise: sum Y
-- statement:
--   Proof of Lemma 13 (Family of checks): the mean of Y is |V|/2^(a−1), which is y = 2|V|/v for v =
--   2^a and a ≥ 1, if a − 1 ≤ s: 2^(a−1) times the sum of Y over all pairs (u₁, u₂) is |V|·|𝔽|².
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/variables/VariableBound/Family/Pairwise.lean#L120-L128
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/variables/VariableBound/Family/Pairwise.lean#L120-L128

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_AppVariablesStatement
import Mathlib.Algebra.Order.BigOperators.Ring.Finset
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Data.Fintype.Fin
import Mathlib.Data.ZMod.Defs
import Mathlib.Tactic.LinearCombination
import Definitions.Def_VariableBound_Family_Pairwise
set_option autoImplicit false
section
section
open VariableBound VariableBound.Pairwise
open Finset AppVariables
variable {F : Type} [Field F] [Fintype F] [DecidableEq F] [Algebra (ZMod 2) F] {m s : ℕ}

theorem VariableBound.Pairwise.sum_Y (bits : F ≃ₗ[ZMod 2] (Fin s → ZMod 2)) (ϑ : Fin m ↪ F) (a : ℕ) (ha : a - 1 ≤ s) (V : Finset (Fin m)) :
    2 ^ (a - 1) * ∑ p : F × F, Y bits ϑ a V p = #V * Fintype.card F ^ 2 := by sorry
