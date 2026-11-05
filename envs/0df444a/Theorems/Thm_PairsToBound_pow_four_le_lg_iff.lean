-- Prove2me | Theorems.Thm_PairsToBound_pow_four_le_lg_iff
-- name    : PairsToBound.pow_four_le_lg_iff
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-05T03:55:43.74206+00:00
-- url     : https://prove2.me/theorems/49970d11-bc3d-44f4-8679-b0b67e3791f4
-- title:
--   Pairs To Bound: pow four le lg iff
-- statement:
--   For natural numbers k ≥ 1 and n: k⁴ ≤ log n if and only if 2^(k⁴) ≤ n.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/variables/PairsToBound/FrontEnd.lean#L77-L93
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/variables/PairsToBound/FrontEnd.lean#L77-L93

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

theorem PairsToBound.pow_four_le_lg_iff {k : ℕ} (hk : 1 ≤ k) (n : ℕ) : (k : ℝ) ^ 4 ≤ lg n ↔ 2 ^ (k ^ 4) ≤ n := by sorry
