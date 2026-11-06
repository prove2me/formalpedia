-- Prove2me | Theorems.Thm_VariableBound_Net_SizeU_totP_eq
-- name    : VariableBound.Net.SizeU.totP_eq
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T03:46:54.905956+00:00
-- url     : https://prove2.me/theorems/8d5a95d7-8fa3-4c89-8c96-4934a3aff988
-- title:
--   Size U: tot P eq
-- statement:
--   μ_κ as a sum over the pairs a < b < g.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/variables/VariableBound/Net/SizeU.lean#L44-L45
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/variables/VariableBound/Net/SizeU.lean#L44-L45

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

theorem VariableBound.Net.SizeU.totP_eq (g : ℕ) (D : Dat) (y κ : ℕ) : totP g D y κ = ∑ b ∈ range g, ∑ a ∈ range b, mu g D y a b κ := by sorry
