-- Prove2me | Theorems.Thm_VariableBound_Count_Vof_eq_empty_iff
-- name    : VariableBound.Count.Vof_eq_empty_iff
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-05T03:49:08.982943+00:00
-- url     : https://prove2.me/theorems/4e906ea4-a2b9-4169-b99a-e0b14ef042a4
-- title:
--   Count: Vof eq empty iff
-- statement:
--   ξ violates no clause iff it satisfies the formula.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/variables/VariableBound/Count/Correct.lean#L45-L56
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/variables/VariableBound/Count/Correct.lean#L45-L56

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

theorem VariableBound.Count.Vof_eq_empty_iff {n : ℕ} (ψ : Fml) (ξ : Fin n → Bool) : Vof ψ ξ = ∅ ↔ ∀ C ∈ ψ, ∃ l ∈ C, Mark.ext ξ l.1 = l.2 := by sorry
