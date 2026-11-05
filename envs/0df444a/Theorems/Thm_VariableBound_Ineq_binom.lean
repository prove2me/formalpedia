-- Prove2me | Theorems.Thm_VariableBound_Ineq_binom
-- name    : VariableBound.Ineq.binom
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-04T16:50:52.437984+00:00
-- url     : https://prove2.me/theorems/c53fa5f4-809d-4b72-b3b5-8109b6306ad4
-- title:
--   Ineq: binom
-- statement:
--   The bound on binomial coefficients of «Setting and parameters»: log C(t, μ) ≤ μ'·max{1,
--   log(3t/μ')} for integers t ≥ 0, 0 ≤ μ ≤ μ' and μ' ≥ 1.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/variables/VariableBound/Params/Ineq.lean#L69-L69
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/variables/VariableBound/Params/Ineq.lean#L69-L69

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_VariableBound_Params_Defs
import Definitions.Def_ClauseBound_ParityChecks_Binom
import Mathlib.Analysis.SpecialFunctions.Log.Deriv
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import Definitions.Def_VariableBound_Params_Ineq
set_option autoImplicit false
section
section
open VariableBound
open AppVariables
open VariableBound.Ineq

theorem VariableBound.Ineq.binom {t μ μ' : ℕ} (h : μ ≤ μ') (h1 : 1 ≤ μ') : lg (t.choose μ) ≤ μ' * max 1 (lg (3 * t / μ')) := by sorry
