-- Prove2me | Theorems.Thm_VariableBound_Count_lg_le_LD
-- name    : VariableBound.Count.lg_le_LD
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T02:04:38.686103+00:00
-- url     : https://prove2.me/theorems/43f4f8a5-8518-483e-98ad-74057b2bffad
-- title:
--   Count: lg le LD
-- statement:
--   log(2Δ) ≤ ⌈log₂(2Δ)⌉, for Δ ≥ 1.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/variables/VariableBound/Count/Correct.lean#L66-L74
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/variables/VariableBound/Count/Correct.lean#L66-L74

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

theorem VariableBound.Count.lg_le_LD (Δ : ℕ) (hΔ : 1 ≤ Δ) : lg (2 * Δ) ≤ LD Δ := by sorry
