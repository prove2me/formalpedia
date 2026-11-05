-- Prove2me | Theorems.Thm_VariableBound_StepParity_choose_mul
-- name    : VariableBound.StepParity.choose_mul
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-04T17:27:03.464317+00:00
-- url     : https://prove2.me/theorems/c39805ca-131d-4d29-9f19-74c2903a8850
-- title:
--   Step Parity: choose mul
-- statement:
--   C(|A|, c)·y as a sum of y over the subsets of A with c elements.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/variables/VariableBound/StepParity.lean#L71-L72
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/variables/VariableBound/StepParity.lean#L71-L72

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

theorem VariableBound.StepParity.choose_mul {E : Type} (A : Finset E) (c : ℕ) (y : ℤ) : ((#A).choose c : ℤ) * y = ∑ _S₀ ∈ A.powerset with #_S₀ = c, y := by sorry
