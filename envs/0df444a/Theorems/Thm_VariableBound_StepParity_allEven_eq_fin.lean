-- Prove2me | Theorems.Thm_VariableBound_StepParity_allEven_eq_fin
-- name    : VariableBound.StepParity.allEven_eq_fin
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-04T15:40:46.08111+00:00
-- url     : https://prove2.me/theorems/c8008079-24cc-4be7-82e4-53a4d2bf8e69
-- title:
--   Step Parity: all Even eq fin
-- statement:
--   The product over the checks of a list is the product over their numbers j : Fin r; check number
--   j is `L.getD j ∅`.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/variables/VariableBound/StepParity.lean#L44-L46
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/variables/VariableBound/StepParity.lean#L44-L46

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

theorem VariableBound.StepParity.allEven_eq_fin (V : X → Finset E) (L : List (Finset E)) (ξ : X) : allEven V L ξ = ∏ j : Fin L.length, ev #(L.getD j ∅ ∩ V ξ) := by sorry
