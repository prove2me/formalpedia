-- Prove2me | Theorems.Thm_PairsToBound_inMainRegime_tests
-- name    : PairsToBound.inMainRegime_tests
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-05T03:53:20.992881+00:00
-- url     : https://prove2.me/theorems/5a595415-620e-4cda-92ef-7f6f6aa65da9
-- title:
--   Pairs To Bound: in Main Regime tests
-- statement:
--   The test is true on the code of (k, φ) if and only if n ≥ K₀^17 and `widthOr3 φ` is at most (log
--   n)^(1/4).
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/variables/PairsToBound/FrontEnd.lean#L104-L108
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/variables/PairsToBound/FrontEnd.lean#L104-L108

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_PairsToBound_Width
import Definitions.Def_VariableBound_Paper_Rename_Defs
import Definitions.Def_VariableBound_Paper_Rename_Code
import Definitions.Def_VariableBound_Paper_Rename_Cert
import Definitions.Def_ClauseBound_Alg_Decode
import Definitions.Def_ToTuring_Poly_NetFun
import Definitions.Def_ToTuring_Closure_Basic
import Definitions.Def_ToTuring_Lib_Bool
import Definitions.Def_ToTuring_Lib_List1b
import Definitions.Def_ToTuring_Lib_Unary
import Mathlib.Analysis.SpecialFunctions.Log.Base
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring
import Definitions.Def_PairsToBound_FrontEnd
set_option autoImplicit false
section
section
open PairsToBound
open Groundwork Groundwork.Prog PaddedDescent.F ClauseBound.Alg MainTheoremForms VariableBound.Rename
open Sat3 (CNF)

theorem PairsToBound.inMainRegime_tests (K₀ : ℕ) : TestsTheMainRegime K₀ (inMainRegime K₀) := by sorry
