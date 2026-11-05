-- Prove2me | Theorems.Thm_VariableBound_Pairwise_second_moment
-- name    : VariableBound.Pairwise.second_moment
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-04T17:32:43.804959+00:00
-- url     : https://prove2.me/theorems/a7a22432-7c87-4bb7-9a0c-ce0640fee872
-- title:
--   Pairwise: second moment
-- statement:
--   Proof of Lemma 13 (Family of checks): Pr(Y > 0) > 2/3 for a set V of more than v = 2^a clauses,
--   if 1 ≤ a and a − 1 ≤ s: three times the number of pairs (u₁, u₂) for which H_E holds for some E ∈ V
--   is more than 2·|𝔽|².
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/variables/VariableBound/Family/Pairwise.lean#L185-L224
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/variables/VariableBound/Family/Pairwise.lean#L185-L224

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

theorem VariableBound.Pairwise.second_moment (bits : F ≃ₗ[ZMod 2] (Fin s → ZMod 2)) (ϑ : Fin m ↪ F) (a : ℕ) (ha1 : 1 ≤ a) (ha : a - 1 ≤ s) (V : Finset (Fin m)) (hV : 2 ^ a < #V) :
    2 * Fintype.card F ^ 2 < 3 * #{p : F × F | ∃ E ∈ V, H bits ϑ a p E} := by sorry
