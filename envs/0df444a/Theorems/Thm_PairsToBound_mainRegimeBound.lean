-- Prove2me | Theorems.Thm_PairsToBound_mainRegimeBound
-- name    : PairsToBound.mainRegimeBound
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T01:22:39.328338+00:00
-- url     : https://prove2.me/theorems/ca9cd03b-db5c-4a09-b858-cc1b5ef3663a
-- title:
--   Pairs To Bound: main Regime Bound
-- statement:
--   «So for n ≥ K₀^17 and 3 ≤ k ≤ (log n)^(1/4) the algorithm of Theorem D (a) takes time
--   2^{O(k²·n·log log n/√(log n))}» (Step 6 of Appendix D), for every machine with the conclusion of
--   Theorem D (a).
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/variables/PairsToBound/Arith.lean#L50-L58
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/variables/PairsToBound/Arith.lean#L50-L58

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_PairsToBound_Defs
import Definitions.Def_VariableBound_Paper_Arith
import Definitions.Def_VariableBound_Printed_VariablesA_StepSparsify
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.SpecialFunctions.Log.Base
import Mathlib.Analysis.SpecialFunctions.Log.Deriv
import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.Analysis.SpecialFunctions.Exponential
import Mathlib.Analysis.Complex.ExponentialBounds
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring
import Mathlib.Tactic.NormNum
import Definitions.Def_PairsToBound_Arith
set_option autoImplicit false
section
section
open PairsToBound
open MainTheoremForms VariableBound.Paper

theorem PairsToBound.mainRegimeBound : MainRegimeBound := by sorry
