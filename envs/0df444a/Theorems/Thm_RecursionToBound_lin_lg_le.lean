-- Prove2me | Theorems.Thm_RecursionToBound_lin_lg_le
-- name    : RecursionToBound.lin_lg_le
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T03:14:39.254332+00:00
-- url     : https://prove2.me/theorems/74d1f575-8bb5-42ab-b4d1-48070f69f9a8
-- title:
--   Recursion To Bound: lin lg le
-- statement:
--   If log n ≥ 900, then 29·(log n + 2) + 19 ≤ n.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/variables/RecursionToBound/Numbers.lean#L192-L196
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/variables/RecursionToBound/Numbers.lean#L192-L196

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

theorem RecursionToBound.lin_lg_le {n : ℕ} (hn : 1 ≤ n) (hL : 900 ≤ lg n) : 29 * (lg n + 2) + 19 ≤ (n : ℝ) := by sorry
