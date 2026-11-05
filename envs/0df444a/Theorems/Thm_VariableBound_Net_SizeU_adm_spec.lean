-- Prove2me | Theorems.Thm_VariableBound_Net_SizeU_adm_spec
-- name    : VariableBound.Net.SizeU.adm_spec
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-05T03:47:01.692748+00:00
-- url     : https://prove2.me/theorems/542b40e7-a25f-4e8b-ac2d-3d60213d82ba
-- title:
--   Size U: adm spec
-- statement:
--   What an admissible profile satisfies: Σ_a μ_(a,0) ≤ n̄ + 1, Σ_a μ_(a,1) ≤ M, and for both kinds
--   μ_κ ≤ (k − 1 + κ)·Σ_a μ_(a,κ) and μ_(a,b,κ) ≤ t_(a,b,κ) for a < b < g.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/variables/VariableBound/Net/SizeU.lean#L49-L63
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/variables/VariableBound/Net/SizeU.lean#L49-L63

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
attribute [local fun_prop] Groundwork.PolyT.length


set_option autoImplicit false
section
section
open VariableBound VariableBound.Net VariableBound.Net.SizeU
open Finset Groundwork AppVariables
variable {k g n nb M : ℕ} {D : Dat} {fl : Bool} {y : ℕ}

theorem VariableBound.Net.SizeU.adm_spec (h : admD k g n nb M D fl y = true) :
    tot g D y 0 ≤ nb + 1 ∧ tot g D y 1 ≤ M ∧ ∀ κ < 2, totP g D y κ ≤ (k - 1 + κ) * tot g D y κ ∧
      ∀ b < g, ∀ a < b, mu g D y a b κ ≤ (tst g n D a b κ).length := by sorry
