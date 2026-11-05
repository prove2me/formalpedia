-- Prove2me | Theorems.Thm_VariableBound_Net_SizeU_nb_mul_sum_le
-- name    : VariableBound.Net.SizeU.nb_mul_sum_le
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-05T03:46:58.156268+00:00
-- url     : https://prove2.me/theorems/46db57b9-6141-46aa-8da5-d46bf3f65766
-- title:
--   Size U: nb mul sum le
-- statement:
--   I ≤ r·s̄: if n̄·|Λ_j| ≤ c for every check, then n̄·I ≤ r·c.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/variables/VariableBound/Net/SizeU.lean#L91-L98
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/variables/VariableBound/Net/SizeU.lean#L91-L98

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

theorem VariableBound.Net.SizeU.nb_mul_sum_le (nb c : ℕ) (Ls : List (List ℕ)) (h : ∀ L ∈ Ls, nb * L.length ≤ c) : nb * (Ls.map List.length).sum ≤ Ls.length * c := by sorry
