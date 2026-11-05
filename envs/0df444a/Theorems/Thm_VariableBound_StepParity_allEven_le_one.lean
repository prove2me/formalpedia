-- Prove2me | Theorems.Thm_VariableBound_StepParity_allEven_le_one
-- name    : VariableBound.StepParity.allEven_le_one
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-04T17:27:00.758038+00:00
-- url     : https://prove2.me/theorems/72a38f37-23f8-48ae-8b70-7c40d8955ce7
-- title:
--   Step Parity: all Even le one
-- statement:
--   The product over j is at most 1.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/variables/VariableBound/StepParity.lean#L66-L68
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/variables/VariableBound/StepParity.lean#L66-L68

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

theorem VariableBound.StepParity.allEven_le_one (V : X → Finset E) (L : List (Finset E)) (ξ : X) : allEven V L ξ ≤ 1 := by sorry
