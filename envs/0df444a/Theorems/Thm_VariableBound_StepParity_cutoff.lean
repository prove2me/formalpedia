-- Prove2me | Theorems.Thm_VariableBound_StepParity_cutoff
-- name    : VariableBound.StepParity.cutoff
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-04T17:30:56.782591+00:00
-- url     : https://prove2.me/theorems/3659e36a-5d04-494f-9199-f7564583526c
-- title:
--   Step Parity: cutoff
-- statement:
--   Lemma 12 (Cut-off), with implicit arguments. Hypotheses: ν ≥ 1 and M' ≥ ν − 1 + r.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/variables/VariableBound/StepParity.lean#L114-L121
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/variables/VariableBound/StepParity.lean#L114-L121

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

theorem VariableBound.StepParity.cutoff (V : X → Finset E) (L : List (Finset E)) (φ : X → ℤ) {ν M' : ℕ} (hν : 1 ≤ ν) (hM : ν - 1 + L.length ≤ M') :
    ∑ ξ, φ ξ * allEven V L ξ ≡ ∑ ξ, φ ξ * ∑ S ∈ tup V L M' ξ, ∏ j, sig #(S j) [ZMOD 2 ^ ν] := by sorry
