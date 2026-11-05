-- Prove2me | Theorems.Thm_VariableBound_StepParity_good_of_Xsum_eq_zero
-- name    : VariableBound.StepParity.good_of_Xsum_eq_zero
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-04T17:28:21.49644+00:00
-- url     : https://prove2.me/theorems/58da96af-8136-4dc3-8d87-a0fb3fbf99ea
-- title:
--   Step Parity: good of Xsum eq zero
-- statement:
--   If X(𝓛) = 0, then every ξ with |V(ξ)| > n̄ violates an odd number of clauses of some check.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/variables/VariableBound/StepParity.lean#L89-L96
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/variables/VariableBound/StepParity.lean#L89-L96

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_AppVariablesStatement
import Definitions.Def_ClauseBound_ParityChecks_StepOne
import Definitions.Def_ClauseBound_ParityChecks_StepOne
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Algebra.BigOperators.ModEq
import Mathlib.Algebra.Order.BigOperators.Ring.Finset
import Mathlib.Data.List.GetD
import Definitions.Def_VariableBound_StepParity
set_option autoImplicit false
section
section
open VariableBound VariableBound.StepParity
open Finset ParityChecks AppVariables
variable {X E : Type} [DecidableEq E]
variable [Fintype X]

theorem VariableBound.StepParity.good_of_Xsum_eq_zero {V : X → Finset E} {nb : ℕ} {L : List (Finset E)} (h : Xsum V nb L = 0) (ξ : X) (hξ : nb < #(V ξ)) :
    ∃ j < L.length, Odd #(L.getD j ∅ ∩ V ξ) := by sorry
