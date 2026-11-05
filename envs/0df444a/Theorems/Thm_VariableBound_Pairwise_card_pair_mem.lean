-- Prove2me | Theorems.Thm_VariableBound_Pairwise_card_pair_mem
-- name    : VariableBound.Pairwise.card_pair_mem
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-04T16:08:43.395832+00:00
-- url     : https://prove2.me/theorems/52c4ef3b-a6da-4f66-ab8d-0e564d56ee81
-- title:
--   Pairwise: card pair mem
-- statement:
--   The number of pairs (u₁, u₂) whose image (u₁ϑ + u₂, u₁ϑ' + u₂), ϑ ≠ ϑ', lies in a set S ⊆ 𝔽² is |S|.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/variables/VariableBound/Family/Pairwise.lean#L90-L91
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/variables/VariableBound/Family/Pairwise.lean#L90-L91

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
omit [Algebra (ZMod 2) F]

theorem VariableBound.Pairwise.card_pair_mem (θ θ' : F) (h : θ ≠ θ') (S : Finset (F × F)) : #{p : F × F | (p.1 * θ + p.2, p.1 * θ' + p.2) ∈ S} = #S := by sorry
