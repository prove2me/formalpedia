-- Prove2me | Theorems.Thm_RecursionToBound_lg_div_le
-- name    : RecursionToBound.lg_div_le
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T01:26:01.081685+00:00
-- url     : https://prove2.me/theorems/a5b42e12-7501-4db6-a7c6-31b5327604be
-- title:
--   Recursion To Bound: lg div le
-- statement:
--   «As e ≥ (log n)^(−C₀) and k ≤ (log n)^(1/4)»: log(k/e) ≤ (C₀ + 1/4)·log log n, for k ≥ 1.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/variables/RecursionToBound/Numbers.lean#L164-L178
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/variables/RecursionToBound/Numbers.lean#L164-L178

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_RecursionToBound_Defs
import Definitions.Def_PairsToBound_Arith
import Definitions.Def_SparsificationLemma_Cal_Alpha
import Definitions.Def_SparsificationLemma_Cal_Beta
import Definitions.Def_VariableBound_Paper_Arith
import Definitions.Def_VariableBound_Printed_VariablesA_Setting
import Definitions.Def_VariableBound_Params_Ineq
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.SpecialFunctions.Log.Base
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.GCongr
import Definitions.Def_RecursionToBound_Numbers
set_option autoImplicit false
section
section
open RecursionToBound
open Finset ClauseBound.ParityChecks UniformInK VariableBound.Net SparsificationLemma MainTheoremForms PairsToBound VariableBound.Paper

theorem RecursionToBound.lg_div_le {k C₀ : ℕ} {L e : ℝ} (hk : 1 ≤ k) (hk4 : (k : ℝ) ^ 4 ≤ L) (he : 1 / L ^ C₀ ≤ e) : lg (k / e) ≤ (C₀ + 1 / 4) * lg L := by sorry
