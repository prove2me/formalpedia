-- Prove2me | Theorems.Thm_VariableBound_StepParity_eta_mul_allEven
-- name    : VariableBound.StepParity.eta_mul_allEven
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-04T17:28:35.392148+00:00
-- url     : https://prove2.me/theorems/58cc0a66-c02b-4d32-a8fb-b07e6353cf59
-- title:
--   Step Parity: eta mul all Even
-- statement:
--   If X(𝓛) = 0, then η(ξ)·∏_j [ |V_j(ξ)| even ] = [V(ξ) = ∅] for every ξ.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/variables/VariableBound/StepParity.lean#L99-L102
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/variables/VariableBound/StepParity.lean#L99-L102

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

theorem VariableBound.StepParity.eta_mul_allEven {V : X → Finset E} {nb : ℕ} {L : List (Finset E)} (h : Xsum V nb L = 0) (ξ : X) :
    eta V nb ξ * allEven V L ξ = if V ξ = ∅ then 1 else 0 := by sorry
