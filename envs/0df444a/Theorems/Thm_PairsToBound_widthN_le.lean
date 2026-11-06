-- Prove2me | Theorems.Thm_PairsToBound_widthN_le
-- name    : PairsToBound.widthN_le
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T03:55:21.19226+00:00
-- url     : https://prove2.me/theorems/5d64f7ad-25ec-46ed-82fe-2c778d748342
-- title:
--   Pairs To Bound: width N le
-- statement:
--   The width is at most 3 plus the number of all literals written in the formula.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/variables/PairsToBound/FrontEnd.lean#L120-L125
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/variables/PairsToBound/FrontEnd.lean#L120-L125

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
import Theorems.Thm_Groundwork_PolyT_flatMap
import Theorems.Thm_Groundwork_PolyT_length
attribute [local fun_prop] Groundwork.PolyT.flatMap
attribute [local fun_prop] Groundwork.PolyT.length


set_option autoImplicit false
section
section
open PairsToBound
open Groundwork Groundwork.Prog PaddedDescent.F ClauseBound.Alg MainTheoremForms VariableBound.Rename
open Sat3 (CNF)
variable {α : Type} [Enc α]

theorem PairsToBound.widthN_le (ψ : Fml) : widthN ψ ≤ (ψ.flatMap fun C => C).length + 3 := by sorry
