-- Prove2me | Theorems.Thm_VariableBound_Net_SizeU_tests_le
-- name    : VariableBound.Net.SizeU.tests_le
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T03:45:46.437385+00:00
-- url     : https://prove2.me/theorems/71f4f9cb-e335-4c6f-9115-783992b037c1
-- title:
--   Size U: tests le
-- statement:
--   Step 3, «The total»: «T₀ ≤ (k − 1)m and T₁ ≤ kr·s̄», the second as T₁ ≤ kI and n̄·I ≤ r·16m,
--   that is I ≤ r·s̄ with s̄ = 16m/n̄. Here T_κ is the sum of the t_(a,b,κ) over the pairs a < b < g and
--   I the number of incidences.
--   Needs k ≥ 1, ψ and the checks well formed, and n̄·|Λ_j| ≤ 16m for every check.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/variables/VariableBound/Net/SizeU.lean#L104-L112
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/variables/VariableBound/Net/SizeU.lean#L104-L112

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_VariableBound_Net_Defs
import Definitions.Def_VariableBound_Net_Tests
import Definitions.Def_VariableBound_Params_Ineq
import Definitions.Def_ClauseBound_ParityChecks_Binom
import Mathlib.Algebra.BigOperators.Intervals
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import Definitions.Def_VariableBound_Net_SizeU
import Theorems.Thm_Groundwork_PolyT_length
import Theorems.Thm_Groundwork_PolyT_map
import Theorems.Thm_Groundwork_PolyT_sum
attribute [local fun_prop] Groundwork.PolyT.length
attribute [local fun_prop] Groundwork.PolyT.map
attribute [local fun_prop] Groundwork.PolyT.sum


set_option autoImplicit false
section
section
open VariableBound VariableBound.Net VariableBound.Net.SizeU
open Finset Groundwork AppVariables
variable {k g n nb M : ℕ} {D : Dat} {fl : Bool} {y : ℕ}

theorem VariableBound.Net.SizeU.tests_le (g : ℕ) (hk : 1 ≤ k) (hW : WfD k n D) (hrow : ∀ L ∈ D.2, nb * L.length ≤ 16 * D.1.length) :
    ∑ b ∈ range g, ∑ a ∈ range b, (tst g n D a b 0).length ≤ (k - 1) * D.1.length ∧
      ∑ b ∈ range g, ∑ a ∈ range b, (tst g n D a b 1).length ≤ k * (D.2.map List.length).sum ∧
      nb * (D.2.map List.length).sum ≤ D.2.length * (16 * D.1.length) := by sorry
