-- Prove2me | Theorems.Thm_VariableBound_Net_SizeU_two_mul_pairs_le
-- name    : VariableBound.Net.SizeU.two_mul_pairs_le
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-05T03:47:17.588212+00:00
-- url     : https://prove2.me/theorems/0748efd9-902d-42a5-8214-1b42f5a0ab57
-- title:
--   Size U: two mul pairs le
-- statement:
--   There are Σ_(b<g) b = g(g − 1)/2 pairs {a, b}: twice their number is at most g².
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/variables/VariableBound/Net/SizeU.lean#L220-L222
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/variables/VariableBound/Net/SizeU.lean#L220-L222

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
set_option autoImplicit false
section
section
open VariableBound VariableBound.Net VariableBound.Net.SizeU
open Finset Groundwork AppVariables
variable {k g n nb M : ℕ} {D : Dat} {fl : Bool} {y : ℕ}

theorem VariableBound.Net.SizeU.two_mul_pairs_le (g : ℕ) : 2 * ∑ b ∈ range g, b ≤ g ^ 2 := by sorry
