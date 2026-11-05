-- Prove2me | Theorems.Thm_VariableBound_VariablesA_lg_div_facts
-- name    : VariableBound.VariablesA.lg_div_facts
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-04T23:58:35.649162+00:00
-- url     : https://prove2.me/theorems/42c1a264-95b6-4dd2-a8c2-ab53837bd394
-- title:
--   Variables A: lg div facts
-- statement:
--   1 ≤ log(k/e) for k ≥ 3 and 0 < e ≤ 1; more precisely log(2/e) ≤ log(k/e) and 1 ≤ log(2/e).
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/variables/VariableBound/Printed/VariablesA/Arith.lean#L30-L35
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/variables/VariableBound/Printed/VariablesA/Arith.lean#L30-L35

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_VariableBound_Printed_ThmVariablesADefs
import Definitions.Def_VariableBound_Printed_VariablesA_Level
import Definitions.Def_ClauseBound_TopN_End
import Definitions.Def_ClauseBound_Alg_End
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import Definitions.Def_VariableBound_Printed_VariablesA_Arith
set_option autoImplicit false
section
section
open VariableBound VariableBound.VariablesA
open Groundwork PaddedDescent.F ClauseBound.Alg ClauseBound.Alg.End ClauseBound.TopN ClauseBound.TopN.End MainTheoremForms
variable {Idx : Type} [Enc Idx] {S : Solver Idx} {e : ℕ → ℝ} {C₀ : ℕ} (Q : S.Seq e C₀)

theorem VariableBound.VariablesA.lg_div_facts {k : ℕ} {x : ℝ} (hk : 3 ≤ k) (h0 : 0 < x) (h1 : x ≤ 1) : 1 ≤ MainTheoremForms.lg (2 / x) ∧ MainTheoremForms.lg (2 / x) ≤ MainTheoremForms.lg (k / x) := by sorry
