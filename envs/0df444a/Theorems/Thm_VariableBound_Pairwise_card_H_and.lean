-- Prove2me | Theorems.Thm_VariableBound_Pairwise_card_H_and
-- name    : VariableBound.Pairwise.card_H_and
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-04T17:31:59.133596+00:00
-- url     : https://prove2.me/theorems/eb4b5a4b-0be4-454c-aee6-e76c7906b741
-- title:
--   Pairwise: card H and
-- statement:
--   Proof of Lemma 13 (Family of checks): the events H_E are pairwise independent, if a − 1 ≤ s: for
--   E ≠ E', 4^(a−1) times the number of pairs (u₁, u₂) with H_E and H_E' is |𝔽|².
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/variables/VariableBound/Family/Pairwise.lean#L107-L116
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/variables/VariableBound/Family/Pairwise.lean#L107-L116

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

theorem VariableBound.Pairwise.card_H_and (bits : F ≃ₗ[ZMod 2] (Fin s → ZMod 2)) (ϑ : Fin m ↪ F) (a : ℕ) (ha : a - 1 ≤ s) (E E' : Fin m) (hE : E ≠ E') :
    4 ^ (a - 1) * #{p : F × F | H bits ϑ a p E ∧ H bits ϑ a p E'} = Fintype.card F ^ 2 := by sorry
