-- Prove2me | Theorems.Thm_VariableBound_Pairwise_sum_Y_sq
-- name    : VariableBound.Pairwise.sum_Y_sq
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-04T17:32:16.17551+00:00
-- url     : https://prove2.me/theorems/4c623b03-31ae-4e0a-ac06-9e04883f703a
-- title:
--   Pairwise: sum Y sq
-- statement:
--   Proof of Lemma 13 (Family of checks): E(Y²) ≤ y² + y (the variance of Y is at most its mean y =
--   2|V|/v), if a − 1 ≤ s: 4^(a−1) times the sum of Y² over all pairs (u₁, u₂) is at most (|V|² +
--   2^(a−1)·|V|)·|𝔽|².
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/variables/VariableBound/Family/Pairwise.lean#L133-L164
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/variables/VariableBound/Family/Pairwise.lean#L133-L164

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

theorem VariableBound.Pairwise.sum_Y_sq (bits : F ≃ₗ[ZMod 2] (Fin s → ZMod 2)) (ϑ : Fin m ↪ F) (a : ℕ) (ha : a - 1 ≤ s) (V : Finset (Fin m)) :
    4 ^ (a - 1) * ∑ p : F × F, Y bits ϑ a V p ^ 2 ≤ (#V ^ 2 + 2 ^ (a - 1) * #V) * Fintype.card F ^ 2 := by sorry
