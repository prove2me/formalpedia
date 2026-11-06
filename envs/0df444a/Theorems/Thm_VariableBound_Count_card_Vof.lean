-- Prove2me | Theorems.Thm_VariableBound_Count_card_Vof
-- name    : VariableBound.Count.card_Vof
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T03:49:49.008389+00:00
-- url     : https://prove2.me/theorems/3cae6387-3373-4846-904d-a878ea41a6e7
-- title:
--   Count: card Vof
-- statement:
--   The number of ξ with V(ξ) = ∅ is the number of satisfying assignments.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/variables/VariableBound/Count/Correct.lean#L59-L61
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/variables/VariableBound/Count/Correct.lean#L59-L61

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_VariableBound_Count_Defs
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring
import Definitions.Def_VariableBound_Count_Correct
set_option autoImplicit false
section
section
open VariableBound VariableBound.Count
open Groundwork Groundwork.Prog PaddedDescent.F PaddedDescent.F.Mark ClauseBound.Alg ClauseBound.ParityChecks AppVariables VariableBound.Net Finset

theorem VariableBound.Count.card_Vof (n : ℕ) (ψ : Fml) : #{ξ : Fin n → Bool | Vof ψ ξ = ∅} = nSat n ψ := by sorry
