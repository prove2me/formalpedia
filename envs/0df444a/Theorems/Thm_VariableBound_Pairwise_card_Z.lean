-- Prove2me | Theorems.Thm_VariableBound_Pairwise_card_Z
-- name    : VariableBound.Pairwise.card_Z
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-04T16:08:20.786669+00:00
-- url     : https://prove2.me/theorems/7235f45b-dc5b-40f2-9e86-f386c20ac8b8
-- title:
--   Pairwise: card Z
-- statement:
--   If a − 1 ≤ s, one element of 𝔽 in 2^(a−1) has its first a − 1 bits equal to 0.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/variables/VariableBound/Family/Pairwise.lean#L58-L70
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/variables/VariableBound/Family/Pairwise.lean#L58-L70

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
omit [DecidableEq F]

theorem VariableBound.Pairwise.card_Z (bits : F ≃ₗ[ZMod 2] (Fin s → ZMod 2)) (a : ℕ) (ha : a - 1 ≤ s) : 2 ^ (a - 1) * #(Z bits a) = Fintype.card F := by sorry
