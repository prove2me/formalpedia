-- Prove2me | Theorems.Thm_VariableBound_Pairwise_card_H
-- name    : VariableBound.Pairwise.card_H
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-04T15:46:30.517121+00:00
-- url     : https://prove2.me/theorems/54d911d5-de87-4521-b38c-88bf0dbb3e79
-- title:
--   Pairwise: card H
-- statement:
--   Proof of Lemma 13 (Family of checks): the event H_E has probability 1/2^(a−1), which is 2/v for
--   v = 2^a and a ≥ 1, if a − 1 ≤ s: 2^(a−1) times the number of pairs (u₁, u₂) with H_E is |𝔽|².
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/variables/VariableBound/Family/Pairwise.lean#L95-L103
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/variables/VariableBound/Family/Pairwise.lean#L95-L103

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

theorem VariableBound.Pairwise.card_H (bits : F ≃ₗ[ZMod 2] (Fin s → ZMod 2)) (ϑ : Fin m ↪ F) (a : ℕ) (ha : a - 1 ≤ s) (E : Fin m) :
    2 ^ (a - 1) * #{p : F × F | H bits ϑ a p E} = Fintype.card F ^ 2 := by sorry
