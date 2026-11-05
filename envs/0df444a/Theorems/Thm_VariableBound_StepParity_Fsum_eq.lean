-- Prove2me | Theorems.Thm_VariableBound_StepParity_Fsum_eq
-- name    : VariableBound.StepParity.Fsum_eq
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-04T16:08:03.131893+00:00
-- url     : https://prove2.me/theorems/ffb918cc-57b2-4434-8a80-a4e97ffa5e3f
-- title:
--   Step Parity: Fsum eq
-- statement:
--   If X(𝓛) = 0, then F(𝓛) is the number of ξ with V(ξ) = ∅.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/variables/VariableBound/StepParity.lean#L105-L109
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/variables/VariableBound/StepParity.lean#L105-L109

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

theorem VariableBound.StepParity.Fsum_eq {V : X → Finset E} {nb : ℕ} {L : List (Finset E)} (h : Xsum V nb L = 0) : Fsum V nb L = #{ξ | V ξ = ∅} := by sorry
